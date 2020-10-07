(*
  File: SepAuto.thy
  Author: Bohua Zhan
*)

section \<open>Separation logic\<close>

theory SepAuto
  imports SepLogic_Base "HOL-Imperative_HOL.Imperative_HOL"
begin

text \<open>
  Separation logic for Imperative\_HOL, and setup of auto2. The development of
  separation logic here follows \cite{Separation_Logic_Imperative_HOL-AFP} by Lammich and Meis.
\<close>

subsection \<open>Partial Heaps\<close>

datatype pheap = pHeap (heapOf: heap) (addrOf: "addr set")
setup \<open>add_simple_datatype "pheap"\<close>

fun in_range :: "(heap \<times> addr set) \<Rightarrow> bool" where
  "in_range (h,as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup \<open>add_rewrite_rule @{thm in_range.simps}\<close>

text \<open>Two heaps agree on a set of addresses.\<close>
definition relH :: "addr set \<Rightarrow> heap \<Rightarrow> heap \<Rightarrow> bool" where [rewrite]:
  "relH as h h' = (in_range (h, as) \<and> in_range (h', as) \<and>
     (\<forall>t. \<forall>a\<in>as. refs h t a = refs h' t a \<and> arrays h t a = arrays h' t a))"

lemma relH_D [forward]:
  "relH as h h' \<Longrightarrow> in_range (h, as) \<and> in_range (h', as)" by auto2

lemma relH_D2 [rewrite]:
  "relH as h h' \<Longrightarrow> a \<in> as \<Longrightarrow> refs h t a = refs h' t a"
  "relH as h h' \<Longrightarrow> a \<in> as \<Longrightarrow> arrays h t a = arrays h' t a" by auto2+
setup \<open>del_prfstep_thm_eqforward @{thm relH_def}\<close>

lemma relH_dist_union [forward]:
  "relH (as \<union> as') h h' \<Longrightarrow> relH as h h' \<and> relH as' h h'" by auto2

lemma relH_ref [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_ref r \<in> as \<Longrightarrow> Ref.get h r = Ref.get h' r"
  by (simp add: Ref.get_def relH_def)

lemma relH_array [rewrite]:
  "relH as h h' \<Longrightarrow> addr_of_array r \<in> as \<Longrightarrow> Array.get h r = Array.get h' r"
  by (simp add: Array.get_def relH_def)

lemma relH_set_ref [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_ref r}} h (Ref.set r x h)"
  by (simp add: Ref.set_def relH_def)

lemma relH_set_array [resolve]:
  "relH {a. a < lim h \<and> a \<notin> {addr_of_array r}} h (Array.set r x h)"
  by (simp add: Array.set_def relH_def)

subsection \<open>Assertions\<close>

datatype assn_raw = Assn (assn_fn: "pheap \<Rightarrow> bool")

fun aseval :: "assn_raw \<Rightarrow> pheap \<Rightarrow> bool" where
  "aseval (Assn f) h = f h"
setup \<open>add_rewrite_rule @{thm aseval.simps}\<close>

definition proper :: "assn_raw \<Rightarrow> bool" where [rewrite]:
  "proper P = (
    (\<forall>h as. aseval P (pHeap h as) \<longrightarrow> in_range (h,as)) \<and>
    (\<forall>h h' as. aseval P (pHeap h as) \<longrightarrow> relH as h h' \<longrightarrow> in_range (h',as) \<longrightarrow> aseval P (pHeap h' as)))"

fun in_range_assn :: "pheap \<Rightarrow> bool" where
  "in_range_assn (pHeap h as) \<longleftrightarrow> (\<forall>a\<in>as. a < lim h)"
setup \<open>add_rewrite_rule @{thm in_range_assn.simps}\<close>

typedef assn = "Collect proper"
@proof @have "Assn in_range_assn \<in> Collect proper" @qed

setup \<open>add_rewrite_rule @{thm Rep_assn_inject}\<close>
setup \<open>register_wellform_data ("Abs_assn P", ["proper P"])\<close>
setup \<open>add_prfstep_check_req ("Abs_assn P", "proper P")\<close>

lemma Abs_assn_inverse' [rewrite]: "proper y \<Longrightarrow> Rep_assn (Abs_assn y) = y"
  by (simp add: Abs_assn_inverse)

lemma proper_Rep_assn [forward]: "proper (Rep_assn P)" using Rep_assn by auto

definition models :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Turnstile>" 50) where [rewrite_bidir]:
  "h \<Turnstile> P \<longleftrightarrow> aseval (Rep_assn P) h"

lemma models_in_range [resolve]: "pHeap h as \<Turnstile> P \<Longrightarrow> in_range (h,as)" by auto2

lemma mod_relH [forward]: "relH as h h' \<Longrightarrow> pHeap h as \<Turnstile> P \<Longrightarrow> pHeap h' as \<Turnstile> P" by auto2

instantiation assn :: one begin
definition one_assn :: assn where [rewrite]:
  "1 \<equiv> Abs_assn (Assn (\<lambda>h. addrOf h = {}))"
instance .. end

abbreviation one_assn :: assn ("emp") where "one_assn \<equiv> 1"

lemma one_assn_rule [rewrite]: "h \<Turnstile> emp \<longleftrightarrow> addrOf h = {}" by auto2
setup \<open>del_prfstep_thm @{thm one_assn_def}\<close>

instantiation assn :: times begin
definition times_assn where [rewrite]:
  "P * Q = Abs_assn (Assn (
    \<lambda>h. (\<exists>as1 as2. addrOf h = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and>
                   aseval (Rep_assn P) (pHeap (heapOf h) as1) \<and> aseval (Rep_assn Q) (pHeap (heapOf h) as2))))"
instance .. end

lemma mod_star_conv [rewrite]:
  "pHeap h as \<Turnstile> A * B \<longleftrightarrow> (\<exists>as1 as2. as = as1 \<union> as2 \<and> as1 \<inter> as2 = {} \<and> pHeap h as1 \<Turnstile> A \<and> pHeap h as2 \<Turnstile> B)" by auto2
setup \<open>del_prfstep_thm @{thm times_assn_def}\<close>

lemma aseval_ext [backward]: "\<forall>h. aseval P h = aseval P' h \<Longrightarrow> P = P'"
  apply (cases P) apply (cases P') by auto

lemma assn_ext: "\<forall>h as. pHeap h as \<Turnstile> P \<longleftrightarrow> pHeap h as \<Turnstile> Q \<Longrightarrow> P = Q"
@proof @have "Rep_assn P = Rep_assn Q" @qed
setup \<open>add_backward_prfstep_cond @{thm assn_ext} [with_filt (order_filter "P" "Q")]\<close>

setup \<open>del_prfstep_thm @{thm aseval_ext}\<close>

lemma assn_one_left: "1 * P = (P::assn)"
@proof
  @have "\<forall>h as. pHeap h as \<Turnstile> P \<longleftrightarrow> pHeap h as \<Turnstile> 1 * P" @with
    @have "as = {} \<union> as"
  @end
@qed

lemma assn_times_comm: "P * Q = Q * (P::assn)"
@proof
  @have "\<forall>h as. pHeap h as \<Turnstile> P * Q \<longleftrightarrow> pHeap h as \<Turnstile> Q * P" @with
    @case "pHeap h as \<Turnstile> P * Q" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "pHeap h as1 \<Turnstile> P" "pHeap h as2 \<Turnstile> Q"
      @have "as = as2 \<union> as1"
    @end
    @case "pHeap h as \<Turnstile> Q * P" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "pHeap h as1 \<Turnstile> Q" "pHeap h as2 \<Turnstile> P"
      @have "as = as2 \<union> as1"
    @end
  @end
@qed

lemma assn_times_assoc: "(P * Q) * R = P * (Q * (R::assn))"
@proof
  @have "\<forall>h as. pHeap h as \<Turnstile> (P * Q) * R \<longleftrightarrow> pHeap h as \<Turnstile> P * (Q * R)" @with
    @case "pHeap h as \<Turnstile> (P * Q) * R" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "pHeap h as1 \<Turnstile> P * Q" "pHeap h as2 \<Turnstile> R"
      @obtain as11 as12 where "as1 = as11 \<union> as12" "as11 \<inter> as12 = {}" "pHeap h as11 \<Turnstile> P" "pHeap h as12 \<Turnstile> Q"
      @have "as = as11 \<union> (as12 \<union> as2)"
    @end
    @case "pHeap h as \<Turnstile> P * (Q * R)" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "pHeap h as1 \<Turnstile> P" "pHeap h as2 \<Turnstile> Q * R"
      @obtain as21 as22 where "as2 = as21 \<union> as22" "as21 \<inter> as22 = {}" "pHeap h as21 \<Turnstile> Q" "pHeap h as22 \<Turnstile> R"
      @have "as = (as1 \<union> as21) \<union> as22"
    @end
  @end
@qed

instantiation assn :: comm_monoid_mult begin
  instance apply standard
  apply (rule assn_times_assoc) apply (rule assn_times_comm) by (rule assn_one_left)
end

subsubsection \<open>Existential Quantification\<close>

definition ex_assn :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "\<exists>\<^sub>A" 11) where [rewrite]:
  "(\<exists>\<^sub>Ax. P x) = Abs_assn (Assn (\<lambda>h. \<exists>x. h \<Turnstile> P x))"

lemma mod_ex_dist [rewrite]: "(h \<Turnstile> (\<exists>\<^sub>Ax. P x)) \<longleftrightarrow> (\<exists>x. h \<Turnstile> P x)" by auto2
setup \<open>del_prfstep_thm @{thm ex_assn_def}\<close>

lemma ex_distrib_star: "(\<exists>\<^sub>Ax. P x * Q) = (\<exists>\<^sub>Ax. P x) * Q"
@proof
  @have "\<forall>h as. pHeap h as \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q \<longleftrightarrow> pHeap h as \<Turnstile> (\<exists>\<^sub>Ax. P x * Q)" @with
    @case "pHeap h as \<Turnstile> (\<exists>\<^sub>Ax. P x) * Q" @with
      @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "pHeap h as1 \<Turnstile> (\<exists>\<^sub>Ax. P x)" "pHeap h as2 \<Turnstile> Q"
      @obtain x where "pHeap h as1 \<Turnstile> P x"
      @have "pHeap h as \<Turnstile> P x * Q"
    @end
  @end
@qed

subsubsection \<open>Pointers\<close>

definition sngr_assn :: "'a::heap ref \<Rightarrow> 'a \<Rightarrow> assn" (infix "\<mapsto>\<^sub>r" 82) where [rewrite]:
  "r \<mapsto>\<^sub>r x = Abs_assn (Assn (
    \<lambda>h. Ref.get (heapOf h) r = x \<and> addrOf h = {addr_of_ref r} \<and> addr_of_ref r < lim (heapOf h)))"

lemma sngr_assn_rule [rewrite]:
  "pHeap h as \<Turnstile> r \<mapsto>\<^sub>r x \<longleftrightarrow> (Ref.get h r = x \<and> as = {addr_of_ref r} \<and> addr_of_ref r < lim h)" by auto2
setup \<open>del_prfstep_thm @{thm sngr_assn_def}\<close>

definition snga_assn :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> assn" (infix "\<mapsto>\<^sub>a" 82) where [rewrite]:
  "r \<mapsto>\<^sub>a x = Abs_assn (Assn (
    \<lambda>h. Array.get (heapOf h) r = x \<and> addrOf h = {addr_of_array r} \<and> addr_of_array r < lim (heapOf h)))"

lemma snga_assn_rule [rewrite]:
  "pHeap h as \<Turnstile> r \<mapsto>\<^sub>a x \<longleftrightarrow> (Array.get h r = x \<and> as = {addr_of_array r} \<and> addr_of_array r < lim h)" by auto2
setup \<open>del_prfstep_thm @{thm snga_assn_def}\<close>

subsubsection \<open>Pure Assertions\<close>

definition pure_assn :: "bool \<Rightarrow> assn" ("\<up>") where [rewrite]:
  "\<up>b = Abs_assn (Assn (\<lambda>h. addrOf h = {} \<and> b))"

lemma pure_assn_rule [rewrite]: "h \<Turnstile> \<up>b \<longleftrightarrow> (addrOf h = {} \<and> b)" by auto2
setup \<open>del_prfstep_thm @{thm pure_assn_def}\<close>

definition top_assn :: assn ("true") where [rewrite]:
  "top_assn = Abs_assn (Assn in_range_assn)"

lemma top_assn_rule [rewrite]: "pHeap h as \<Turnstile> true \<longleftrightarrow> in_range (h, as)" by auto2
setup \<open>del_prfstep_thm @{thm top_assn_def}\<close>

setup \<open>del_prfstep_thm @{thm models_def}\<close>

subsubsection \<open>Properties of assertions\<close>

abbreviation bot_assn :: assn ("false") where "bot_assn \<equiv> \<up>False"

lemma top_assn_reduce: "true * true = true"
@proof
  @have "\<forall>h. h \<Turnstile> true \<longleftrightarrow> h \<Turnstile> true * true" @with
    @have "addrOf h = addrOf h \<union> {}"
  @end
@qed

lemma mod_pure_star_dist [rewrite]:
  "h \<Turnstile> P * \<up>b \<longleftrightarrow> (h \<Turnstile> P \<and> b)"
@proof
  @case "h \<Turnstile> P \<and> b" @with
    @have "addrOf h = addrOf h \<union> {}"
  @end
@qed

lemma pure_conj: "\<up>(P \<and> Q) = \<up>P * \<up>Q" by auto2

subsubsection \<open>Entailment and its properties\<close>

definition entails :: "assn \<Rightarrow> assn \<Rightarrow> bool" (infix "\<Longrightarrow>\<^sub>A" 10) where [rewrite]:
  "(P \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<forall>h. h \<Turnstile> P \<longrightarrow> h \<Turnstile> Q)"

lemma entails_triv: "A \<Longrightarrow>\<^sub>A A" by auto2
lemma entails_true: "A \<Longrightarrow>\<^sub>A true" by auto2
lemma entails_frame [backward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> P * R \<Longrightarrow>\<^sub>A Q * R" by auto2
lemma entails_frame': "\<not> (A * F \<Longrightarrow>\<^sub>A Q) \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not> (B * F \<Longrightarrow>\<^sub>A Q)" by auto2
lemma entails_frame'': "\<not> (P \<Longrightarrow>\<^sub>A B * F) \<Longrightarrow> A \<Longrightarrow>\<^sub>A B \<Longrightarrow> \<not> (P \<Longrightarrow>\<^sub>A A * F)" by auto2
lemma entails_equiv_forward: "P = Q \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q" by auto2
lemma entails_equiv_backward: "P = Q \<Longrightarrow> Q \<Longrightarrow>\<^sub>A P" by auto2
lemma entailsD [forward]: "P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> h \<Turnstile> P \<Longrightarrow> h \<Turnstile> Q" by auto2
lemma entails_trans2: "A \<Longrightarrow>\<^sub>A D * B \<Longrightarrow> B \<Longrightarrow>\<^sub>A C \<Longrightarrow> A \<Longrightarrow>\<^sub>A D * C" by auto2

lemma entails_pure': "\<not>(\<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<not>(emp \<Longrightarrow>\<^sub>A Q) \<and> b)" by auto2
lemma entails_pure: "\<not>(P * \<up>b \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<not>(P \<Longrightarrow>\<^sub>A Q) \<and> b)" by auto2
lemma entails_ex: "\<not>((\<exists>\<^sub>Ax. P x) \<Longrightarrow>\<^sub>A Q) \<longleftrightarrow> (\<exists>x. \<not>(P x \<Longrightarrow>\<^sub>A Q))" by auto2
lemma entails_ex_post: "\<not>(P \<Longrightarrow>\<^sub>A (\<exists>\<^sub>Ax. Q x)) \<Longrightarrow> \<forall>x. \<not>(P \<Longrightarrow>\<^sub>A Q x)" by auto2
lemma entails_pure_post: "\<not>(P \<Longrightarrow>\<^sub>A Q * \<up>b) \<Longrightarrow> P \<Longrightarrow>\<^sub>A Q \<Longrightarrow> \<not>b" by auto2

setup \<open>del_prfstep_thm @{thm entails_def}\<close>

subsection \<open>Definition of the run predicate\<close>

inductive run :: "'a Heap \<Rightarrow> heap option \<Rightarrow> heap option \<Rightarrow> 'a \<Rightarrow> bool" where
  "run c None None r"
| "execute c h = None \<Longrightarrow> run c (Some h) None r"
| "execute c h = Some (r, h') \<Longrightarrow> run c (Some h) (Some h') r"
setup \<open>add_case_induct_rule @{thm run.cases}\<close>
setup \<open>fold add_resolve_prfstep @{thms run.intros(1,2)}\<close>
setup \<open>add_forward_prfstep @{thm run.intros(3)}\<close>

lemma run_complete [resolve]:
  "\<exists>\<sigma>' r. run c \<sigma> \<sigma>' (r::'a)"
@proof
  @obtain "r::'a" where "r = r"
  @case "\<sigma> = None" @with @have "run c None None r" @end
  @case "execute c (the \<sigma>) = None" @with @have "run c \<sigma> None r" @end
@qed

lemma run_to_execute [forward]:
  "run c (Some h) \<sigma>' r \<Longrightarrow> if \<sigma>' = None then execute c h = None else execute c h = Some (r, the \<sigma>')"
@proof @case_induct "run c (Some h) \<sigma>' r" @qed

setup \<open>add_rewrite_rule @{thm execute_bind(1)}\<close>
lemma runE [forward]:
  "run f (Some h) (Some h') r' \<Longrightarrow> run (f \<bind> g) (Some h) \<sigma> r \<Longrightarrow> run (g r') (Some h') \<sigma> r" by auto2

setup \<open>add_rewrite_rule @{thm Array.get_alloc}\<close>
setup \<open>add_rewrite_rule @{thm Ref.get_alloc}\<close>
setup \<open>add_rewrite_rule_bidir @{thm Array.length_def}\<close>

subsection \<open>Definition of hoare triple, and the frame rule.\<close>

definition new_addrs :: "heap \<Rightarrow> addr set \<Rightarrow> heap \<Rightarrow> addr set" where [rewrite]:
  "new_addrs h as h' = as \<union> {a. lim h \<le> a \<and> a < lim h'}"

definition hoare_triple :: "assn \<Rightarrow> 'a Heap \<Rightarrow> ('a \<Rightarrow> assn) \<Rightarrow> bool" ("<_>/ _/ <_>") where [rewrite]:
  "<P> c <Q> \<longleftrightarrow> (\<forall>h as \<sigma> r. pHeap h as \<Turnstile> P \<longrightarrow> run c (Some h) \<sigma> r \<longrightarrow>
    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) \<Turnstile> Q r \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>)))"

lemma hoare_tripleD [forward]:
  "<P> c <Q> \<Longrightarrow> run c (Some h) \<sigma> r \<Longrightarrow> \<forall>as. pHeap h as \<Turnstile> P \<longrightarrow>
     (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) \<Turnstile> Q r \<and> relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and>
     lim h \<le> lim (the \<sigma>))"
  by auto2
setup \<open>del_prfstep_thm_eqforward @{thm hoare_triple_def}\<close>

abbreviation hoare_triple' :: "assn \<Rightarrow> 'r Heap \<Rightarrow> ('r \<Rightarrow> assn) \<Rightarrow> bool" ("<_> _ <_>\<^sub>t") where
  "<P> c <Q>\<^sub>t \<equiv> <P> c <\<lambda>r. Q r * true>"

theorem frame_rule [backward]:
  "<P> c <Q> \<Longrightarrow> <P * R> c <\<lambda>x. Q x * R>"
@proof
  @have "\<forall>h as \<sigma> r. pHeap h as \<Turnstile> P * R \<longrightarrow> run c (Some h) \<sigma> r \<longrightarrow>
                    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) \<Turnstile> Q r * R \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    @obtain as1 as2 where "as = as1 \<union> as2" "as1 \<inter> as2 = {}" "pHeap h as1 \<Turnstile> P \<and> pHeap h as2 \<Turnstile> R"
    @have "relH as2 h (the \<sigma>)"
    @have "new_addrs h as (the \<sigma>) = new_addrs h as1 (the \<sigma>) \<union> as2"
  @end
@qed

text \<open>This is the last use of the definition of separating conjunction.\<close>
setup \<open>del_prfstep_thm @{thm mod_star_conv}\<close>

theorem bind_rule:
  "<P> f <Q> \<Longrightarrow> \<forall>x. <Q x> g x <R> \<Longrightarrow> <P> f \<bind> g <R>"
@proof
  @have "\<forall>h as \<sigma> r. pHeap h as \<Turnstile> P \<longrightarrow> run (f \<bind> g) (Some h) \<sigma> r \<longrightarrow>
                    (\<sigma> \<noteq> None \<and> pHeap (the \<sigma>) (new_addrs h as (the \<sigma>)) \<Turnstile> R r \<and>
                     relH {a . a < lim h \<and> a \<notin> as} h (the \<sigma>) \<and> lim h \<le> lim (the \<sigma>))" @with
    \<comment> \<open>First step from h to h'\<close>
    @obtain \<sigma>' r' where "run f (Some h) \<sigma>' r'"
    @obtain h' where "\<sigma>' = Some h'"
    @let "as' = new_addrs h as h'"
    @have "pHeap h' as' \<Turnstile> Q r'"

    \<comment> \<open>Second step from h' to h''\<close>
    @have "run (g r') (Some h') \<sigma> r"
    @obtain h'' where "\<sigma> = Some h''"
    @let "as'' = new_addrs h' as' h''"
    @have "pHeap h'' as'' \<Turnstile> R r"
    @have "as'' = new_addrs h as h''"
  @end
@qed

text \<open>Actual statement used:\<close>
lemma bind_rule':
  "<P> f <Q> \<Longrightarrow> \<not> <P> f \<bind> g <R> \<Longrightarrow> \<exists>x. \<not> <Q x> g x <R>" using bind_rule by blast

lemma pre_rule':
  "\<not> <P * R> f <Q> \<Longrightarrow> P \<Longrightarrow>\<^sub>A P' \<Longrightarrow> \<not> <P' * R> f <Q>"
@proof @have "P * R \<Longrightarrow>\<^sub>A P' * R" @qed

lemma pre_rule'':
  "<P> f <Q> \<Longrightarrow> P' \<Longrightarrow>\<^sub>A P * R \<Longrightarrow> <P'> f <\<lambda>x. Q x * R>"
@proof @have "<P * R> f <\<lambda>x. Q x * R>" @qed

lemma pre_ex_rule:
  "\<not> <\<exists>\<^sub>Ax. P x> f <Q> \<longleftrightarrow> (\<exists>x. \<not> <P x> f <Q>)" by auto2

lemma pre_pure_rule:
  "\<not> <P * \<up>b> f <Q> \<longleftrightarrow> \<not> <P> f <Q> \<and> b" by auto2

lemma pre_pure_rule':
  "\<not> <\<up>b> f <Q> \<longleftrightarrow> \<not> <emp> f <Q> \<and> b" by auto2

lemma post_rule:
  "<P> f <Q> \<Longrightarrow> \<forall>x. Q x \<Longrightarrow>\<^sub>A R x \<Longrightarrow> <P> f <R>" by auto2

setup \<open>fold del_prfstep_thm [@{thm entailsD}, @{thm entails_frame}, @{thm frame_rule}]\<close>

text \<open>Actual statement used:\<close>
lemma post_rule':
  "<P> f <Q> \<Longrightarrow> \<not> <P> f <R> \<Longrightarrow> \<exists>x. \<not> (Q x \<Longrightarrow>\<^sub>A R x)" using post_rule by blast

lemma norm_pre_pure_iff: "<P * \<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <P> c <Q>)" by auto2
lemma norm_pre_pure_iff2: "<\<up>b> c <Q> \<longleftrightarrow> (b \<longrightarrow> <emp> c <Q>)" by auto2

subsection \<open>Hoare triples for atomic commands\<close>

text \<open>First, those that do not modify the heap.\<close>
setup \<open>add_rewrite_rule @{thm execute_assert(1)}\<close>
lemma assert_rule:
  "<\<up>(R x)> assert R x <\<lambda>r. \<up>(r = x)>" by auto2

lemma execute_return' [rewrite]: "execute (return x) h = Some (x, h)" by (metis comp_eq_dest_lhs execute_return)
lemma return_rule:
  "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_nth(1)}\<close>
lemma nth_rule:
  "<a \<mapsto>\<^sub>a xs * \<up>(i < length xs)> Array.nth a i <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs ! i)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_len}\<close>
lemma length_rule:
  "<a \<mapsto>\<^sub>a xs> Array.len a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = length xs)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_lookup}\<close>
lemma lookup_rule:
  "<p \<mapsto>\<^sub>r x> !p <\<lambda>r. p \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_freeze}\<close>
lemma freeze_rule:
  "<a \<mapsto>\<^sub>a xs> Array.freeze a <\<lambda>r. a \<mapsto>\<^sub>a xs * \<up>(r = xs)>" by auto2

text \<open>Next, the update rules.\<close>
setup \<open>add_rewrite_rule @{thm Ref.lim_set}\<close>
lemma Array_lim_set [rewrite]: "lim (Array.set p xs h) = lim h" by (simp add: Array.set_def)

setup \<open>fold add_rewrite_rule [@{thm Ref.get_set_eq}, @{thm Array.get_set_eq}]\<close>
setup \<open>add_rewrite_rule @{thm Array.update_def}\<close>

setup \<open>add_rewrite_rule @{thm execute_upd(1)}\<close>
lemma upd_rule:
  "<a \<mapsto>\<^sub>a xs * \<up>(i < length xs)> Array.upd i x a <\<lambda>r. a \<mapsto>\<^sub>a list_update xs i x * \<up>(r = a)>" by auto2

setup \<open>add_rewrite_rule @{thm execute_update}\<close>
lemma update_rule:
  "<p \<mapsto>\<^sub>r y> p := x <\<lambda>r. p \<mapsto>\<^sub>r x>" by auto2

text \<open>Finally, the allocation rules.\<close>
lemma lim_set_gen [rewrite]: "lim (h\<lparr>lim := l\<rparr>) = l" by simp

lemma Array_alloc_def' [rewrite]: 
  "Array.alloc xs h = (let l = lim h; r = Array l in (r, (Array.set r xs (h\<lparr>lim := l + 1\<rparr>))))"
  by (simp add: Array.alloc_def)

setup \<open>fold add_rewrite_rule [
  @{thm addr_of_array.simps}, @{thm addr_of_ref.simps}, @{thm Ref.alloc_def}]\<close>

lemma refs_on_Array_set [rewrite]: "refs (Array.set p xs h) t i = refs h t i"
  by (simp add: Array.set_def)

lemma arrays_on_Ref_set [rewrite]: "arrays (Ref.set p x h) t i = arrays h t i"
  by (simp add: Ref.set_def)

lemma refs_on_Array_alloc [rewrite]: "refs (snd (Array.alloc xs h)) t i = refs h t i"
  by (metis (no_types, lifting) Array.alloc_def refs_on_Array_set select_convs(2) snd_conv surjective update_convs(3))

lemma arrays_on_Ref_alloc [rewrite]: "arrays (snd (Ref.alloc x h)) t i = arrays h t i"
  by (metis (no_types, lifting) Ref.alloc_def arrays_on_Ref_set select_convs(1) sndI surjective update_convs(3))

lemma arrays_on_Array_alloc [rewrite]: "i < lim h \<Longrightarrow> arrays (snd (Array.alloc xs h)) t i = arrays h t i"
  by (smt Array.alloc_def Array.set_def addr_of_array.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less simps(1) snd_conv surjective update_convs(1) update_convs(3))

lemma refs_on_Ref_alloc [rewrite]: "i < lim h \<Longrightarrow> refs (snd (Ref.alloc x h)) t i = refs h t i"
  by (smt Ref.alloc_def Ref.set_def addr_of_ref.simps fun_upd_apply less_or_eq_imp_le
          linorder_not_less select_convs(2) simps(6) snd_conv surjective update_convs(3))

setup \<open>add_rewrite_rule @{thm execute_new}\<close>
lemma new_rule:
  "<emp> Array.new n x <\<lambda>r. r \<mapsto>\<^sub>a replicate n x>" by auto2

setup \<open>add_rewrite_rule @{thm execute_of_list}\<close>
lemma of_list_rule:
  "<emp> Array.of_list xs <\<lambda>r. r \<mapsto>\<^sub>a xs>" by auto2

setup \<open>add_rewrite_rule @{thm execute_ref}\<close>
lemma ref_rule:
  "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2

setup \<open>fold del_prfstep_thm [
  @{thm sngr_assn_rule}, @{thm snga_assn_rule}, @{thm pure_assn_rule}, @{thm top_assn_rule},
  @{thm mod_pure_star_dist}, @{thm one_assn_rule}, @{thm hoare_triple_def}, @{thm mod_ex_dist}]\<close>
setup \<open>del_simple_datatype "pheap"\<close>

subsection \<open>Definition of procedures\<close>

text \<open>ASCII abbreviations for ML files.\<close>
abbreviation (input) ex_assn_ascii :: "('a \<Rightarrow> assn) \<Rightarrow> assn" (binder "EXA" 11)
  where "ex_assn_ascii \<equiv> ex_assn"

abbreviation (input) models_ascii :: "pheap \<Rightarrow> assn \<Rightarrow> bool" (infix "|=" 50)
  where "h |= P \<equiv> h \<Turnstile> P"

ML_file "sep_util.ML"

ML \<open>
structure AssnMatcher = AssnMatcher(SepUtil)
structure SepLogic = SepLogic(SepUtil)
val add_assn_matcher = AssnMatcher.add_assn_matcher
val add_entail_matcher = AssnMatcher.add_entail_matcher
val add_forward_ent_prfstep = SepLogic.add_forward_ent_prfstep
val add_rewrite_ent_rule = SepLogic.add_rewrite_ent_rule
val add_hoare_triple_prfstep = SepLogic.add_hoare_triple_prfstep
\<close>
setup \<open>AssnMatcher.add_assn_matcher_proofsteps\<close>
setup \<open>SepLogic.add_sep_logic_proofsteps\<close>

ML_file "sep_steps_test.ML"

attribute_setup forward_ent = \<open>setup_attrib add_forward_ent_prfstep\<close>
attribute_setup rewrite_ent = \<open>setup_attrib add_rewrite_ent_rule\<close>
attribute_setup hoare_triple = \<open>setup_attrib add_hoare_triple_prfstep\<close>

setup \<open>fold add_hoare_triple_prfstep [
  @{thm assert_rule}, @{thm update_rule}, @{thm nth_rule}, @{thm upd_rule},
  @{thm return_rule}, @{thm ref_rule}, @{thm lookup_rule}, @{thm new_rule},
  @{thm of_list_rule}, @{thm length_rule}, @{thm freeze_rule}]\<close>

text \<open>Some simple tests\<close>

theorem "<emp> ref x <\<lambda>r. r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> ref x <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<a \<mapsto>\<^sub>r x> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!a) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = x)>" by auto2
theorem "<a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y> (!b) <\<lambda>r. a \<mapsto>\<^sub>r x * b \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; !a } <\<lambda>r. a \<mapsto>\<^sub>r y * \<up>(r = y)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { a := y; a := z; !a } <\<lambda>r. a \<mapsto>\<^sub>r z * \<up>(r = z)>" by auto2
theorem "<a \<mapsto>\<^sub>r x> do { y \<leftarrow> !a; ref y} <\<lambda>r. a \<mapsto>\<^sub>r x * r \<mapsto>\<^sub>r x>" by auto2
theorem "<emp> return x <\<lambda>r. \<up>(r = x)>" by auto2

end
