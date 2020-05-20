(******************************************************************************)
(* Project: Isabelle/UTP Toolkit                                              *)
(* File: Countable_Set_Extra.thy                                              *)
(* Authors: Simon Foster and Frank Zeyda                                      *)
(* Emails: simon.foster@york.ac.uk and frank.zeyda@york.ac.uk                 *)
(******************************************************************************)

section \<open> Countable Sets: Extra functions and properties \<close>

theory Countable_Set_Extra
imports
  "HOL-Library.Countable_Set_Type"
  Sequence
  FSet_Extra
begin

subsection \<open> Extra syntax \<close>

notation cempty ("{}\<^sub>c")
notation cin (infix "\<in>\<^sub>c" 50)
notation cUn (infixl "\<union>\<^sub>c" 65)
notation cInt (infixl "\<inter>\<^sub>c" 70)
notation cDiff (infixl "-\<^sub>c" 65)
notation cUnion ("\<Union>\<^sub>c_" [900] 900)
notation cimage (infixr "`\<^sub>c" 90)

abbreviation csubseteq :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> bool" ("(_/ \<subseteq>\<^sub>c _)" [51, 51] 50)
where "A \<subseteq>\<^sub>c B \<equiv> A \<le> B"

abbreviation csubset :: "'a cset \<Rightarrow> 'a cset \<Rightarrow> bool" ("(_/ \<subset>\<^sub>c _)" [51, 51] 50)
where "A \<subset>\<^sub>c B \<equiv> A < B"

subsection \<open> Countable set functions \<close>

setup_lifting type_definition_cset

lift_definition cnin :: "'a \<Rightarrow> 'a cset \<Rightarrow> bool" (infix "\<notin>\<^sub>c" 50) is "(\<notin>)" .

definition cBall :: "'a cset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"cBall A P = (\<forall>x. x \<in>\<^sub>c A \<longrightarrow> P x)"

definition cBex :: "'a cset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" where
"cBex A P = (\<exists>x. x \<in>\<^sub>c A \<longrightarrow> P x)"

declare cBall_def [mono,simp]
declare cBex_def [mono,simp]

syntax
  "_cBall" :: "pttrn => 'a cset => bool => bool" ("(3\<forall> _\<in>\<^sub>c_./ _)" [0, 0, 10] 10)
  "_cBex"  :: "pttrn => 'a cset => bool => bool" ("(3\<exists> _\<in>\<^sub>c_./ _)" [0, 0, 10] 10)

translations
  "\<forall> x\<in>\<^sub>cA. P" == "CONST cBall A (%x. P)"
  "\<exists> x\<in>\<^sub>cA. P" == "CONST cBex  A (%x. P)"

definition cset_Collect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a cset" where
"cset_Collect = (acset o Collect)"

lift_definition cset_Coll :: "'a cset \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a cset" is "\<lambda> A P. {x \<in> A. P x}"
  by (auto)

lemma cset_Coll_equiv: "cset_Coll A P = cset_Collect (\<lambda> x. x \<in>\<^sub>c A \<and> P x)"
  by (simp add:cset_Collect_def cset_Coll_def cin_def)

declare cset_Collect_def [simp]

syntax
  "_cColl" :: "pttrn => bool => 'a cset" ("(1{_./ _}\<^sub>c)")

translations
  "{x . P}\<^sub>c" \<rightleftharpoons> "(CONST cset_Collect) (\<lambda> x . P)"

syntax (xsymbols)
  "_cCollect" :: "pttrn => 'a cset => bool => 'a cset"    ("(1{_ \<in>\<^sub>c/ _./ _}\<^sub>c)")
translations
  "{x \<in>\<^sub>c A. P}\<^sub>c" => "CONST cset_Coll A (\<lambda> x. P)"

lemma cset_CollectI: "P (a :: 'a::countable) \<Longrightarrow> a \<in>\<^sub>c {x. P x}\<^sub>c"
  by (simp add: cin_def)

lemma cset_CollI: "\<lbrakk> a \<in>\<^sub>c A; P a \<rbrakk> \<Longrightarrow> a \<in>\<^sub>c {x \<in>\<^sub>c A. P x}\<^sub>c"
  by (simp add: cin.rep_eq cset_Coll.rep_eq)

lemma cset_CollectD: "(a :: 'a::countable) \<in>\<^sub>c {x. P x}\<^sub>c \<Longrightarrow> P a"
  by (simp add: cin_def)

lemma cset_Collect_cong: "(\<And>x. P x = Q x) ==> {x. P x}\<^sub>c = {x. Q x}\<^sub>c"
  by simp

text \<open> Avoid eta-contraction for robust pretty-printing. \<close>

print_translation \<open>
 [Syntax_Trans.preserve_binder_abs_tr'
   @{const_syntax cset_Collect} @{syntax_const "_cColl"}]
\<close>

lift_definition cset_set :: "'a list \<Rightarrow> 'a cset" is set
  using countable_finite by blast

lemma countable_finite_power:
  "countable(A) \<Longrightarrow> countable {B. B \<subseteq> A \<and> finite(B)}"
  by (metis Collect_conj_eq Int_commute countable_Collect_finite_subset)

lift_definition cInter :: "'a cset cset \<Rightarrow> 'a cset"  ("\<Inter>\<^sub>c_" [900] 900)
  is "\<lambda>A. if A = {} then {} else \<Inter> A"
  using countable_INT [of _ _ id] by auto

abbreviation (input) cINTER :: "'a cset \<Rightarrow> ('a \<Rightarrow> 'b cset) \<Rightarrow> 'b cset"
  where "cINTER A f \<equiv> cInter (cimage f A)"

lift_definition cfinite :: "'a cset \<Rightarrow> bool" is finite .
lift_definition cInfinite :: "'a cset \<Rightarrow> bool" is infinite .
lift_definition clist :: "'a::linorder cset \<Rightarrow> 'a list" is sorted_list_of_set .
lift_definition ccard :: "'a cset \<Rightarrow> nat" is card .
lift_definition cPow :: "'a cset \<Rightarrow> 'a cset cset" is "\<lambda> A. {B. B \<subseteq>\<^sub>c A \<and> cfinite(B)}"
proof -
  fix A
  have "{B :: 'a cset. B \<subseteq>\<^sub>c A \<and> cfinite B} = acset ` {B :: 'a set. B \<subseteq> rcset A \<and> finite B}"
    apply (auto simp add: cfinite.rep_eq cin_def less_eq_cset_def countable_finite)
    using image_iff apply fastforce
    done

  moreover have "countable {B :: 'a set. B \<subseteq> rcset A \<and> finite B}"
    by (auto intro: countable_finite_power)

  ultimately show "countable {B. B \<subseteq>\<^sub>c A \<and> cfinite B}"
    by simp
qed

definition CCollect :: "('a \<Rightarrow> bool option) \<Rightarrow> 'a cset option" where
"CCollect p = (if (None \<notin> range p) then Some (cset_Collect (the \<circ> p)) else None)"

definition cset_mapM :: "'a option cset \<Rightarrow> 'a cset option" where
"cset_mapM A = (if (None \<in>\<^sub>c A) then None else Some (the `\<^sub>c A))"

lemma cset_mapM_Some_image [simp]:
  "cset_mapM (cimage Some A) = Some A"
  apply (auto simp add: cset_mapM_def)
  apply (metis cimage_cinsert cinsertI1 option.sel set_cinsert)
  done

definition CCollect_ext :: "('a \<Rightarrow> 'b option) \<Rightarrow> ('a \<Rightarrow> bool option) \<Rightarrow> 'b cset option" where
"CCollect_ext f p = do { xs \<leftarrow> CCollect p; cset_mapM (f `\<^sub>c xs) }"

lemma the_Some_image [simp]:
  "the ` Some ` xs = xs"
  by (auto simp add:image_iff)

lemma CCollect_ext_Some [simp]:
  "CCollect_ext Some xs = CCollect xs"
  apply (case_tac "CCollect xs")
   apply (auto simp add:CCollect_ext_def)
  done

lift_definition list_of_cset :: "'a :: linorder cset \<Rightarrow> 'a list" is sorted_list_of_set .

lift_definition fset_cset :: "'a fset \<Rightarrow> 'a cset" is id
  using uncountable_infinite by auto

definition cset_count :: "'a cset \<Rightarrow> 'a \<Rightarrow> nat" where
"cset_count A =
  (if (finite (rcset A))
   then (SOME f::'a\<Rightarrow>nat. inj_on f (rcset A))
   else (SOME f::'a\<Rightarrow>nat. bij_betw f (rcset A) UNIV))"

lemma cset_count_inj_seq:
  "inj_on (cset_count A) (rcset A)"
proof (cases "finite (rcset A)")
  case True note fin = this
  obtain count :: "'a \<Rightarrow> nat" where count_inj: "inj_on count (rcset A)"
    by (metis countable_def mem_Collect_eq rcset)
  with fin show ?thesis
    by (metis (poly_guards_query) cset_count_def someI_ex)
next
  case False note inf = this
  obtain count :: "'a \<Rightarrow> nat" where count_bij: "bij_betw count (rcset A) UNIV"
    by (metis countableE_infinite inf mem_Collect_eq rcset)
  with inf have "bij_betw (cset_count A) (rcset A) UNIV"
    by (metis (poly_guards_query) cset_count_def someI_ex)
  thus ?thesis
    by (metis bij_betw_imp_inj_on)
qed

lemma cset_count_infinite_bij:
  assumes "infinite (rcset A)"
  shows "bij_betw (cset_count A) (rcset A) UNIV"
proof -
  from assms obtain count :: "'a \<Rightarrow> nat" where count_bij: "bij_betw count (rcset A) UNIV"
    by (metis countableE_infinite mem_Collect_eq rcset)
  with assms show ?thesis
    by (metis (poly_guards_query) cset_count_def someI_ex)
qed

definition cset_seq :: "'a cset \<Rightarrow> (nat \<rightharpoonup> 'a)" where
"cset_seq A i = (if (i \<in> range (cset_count A) \<and> inv_into (rcset A) (cset_count A) i \<in>\<^sub>c A)
                 then Some (inv_into (rcset A) (cset_count A) i)
                 else None)"

lemma cset_seq_ran: "ran (cset_seq A) = rcset(A)"
  apply (auto simp add: ran_def cset_seq_def cin.rep_eq)
  apply (metis cset_count_inj_seq inv_into_f_f rangeI)
  done

lemma cset_seq_inj: "inj cset_seq"
proof (rule injI)
  fix A B :: "'a cset"
  assume "cset_seq A = cset_seq B"
  thus "A = B"
    by (metis cset_seq_ran rcset_inverse)
qed

lift_definition cset2seq :: "'a cset \<Rightarrow> 'a seq"
is "(\<lambda> A i. if (i \<in> cset_count A ` rcset A) then inv_into (rcset A) (cset_count A) i else (SOME x. x \<in>\<^sub>c A))" .

lemma range_cset2seq:
  "A \<noteq> {}\<^sub>c \<Longrightarrow> range (Rep_seq (cset2seq A)) = rcset A"
  by (force intro: someI2 simp add: cset2seq.rep_eq cset_count_inj_seq bot_cset.rep_eq cin.rep_eq)

lemma infinite_cset_count_surj: "infinite (rcset A) \<Longrightarrow> surj (cset_count A)"
  using bij_betw_imp_surj cset_count_infinite_bij by auto

lemma cset2seq_inj:
  "inj_on cset2seq {A. A \<noteq> {}\<^sub>c}"
  apply (rule inj_onI)
  apply (simp)
  apply (metis range_cset2seq rcset_inject)
  done

lift_definition nat_seq2set :: "nat seq \<Rightarrow> nat set" is
"\<lambda> f. prod_encode ` {(x, f x) | x. True}" .

lemma inj_nat_seq2set: "inj nat_seq2set"
proof (rule injI, transfer)
  fix f g
  assume "prod_encode ` {(x, f x) |x. True} = prod_encode ` {(x, g x) |x. True}"
  hence "{(x, f x) |x. True} = {(x, g x) |x. True}"
    by (simp add: inj_image_eq_iff[OF inj_prod_encode])
  thus "f = g"
    by (auto simp add: set_eq_iff)
qed

lift_definition bit_seq_of_nat_set :: "nat set \<Rightarrow> bool seq"
is "\<lambda> A i. i \<in> A" .

lemma bit_seq_of_nat_set_inj: "inj bit_seq_of_nat_set"
  apply (rule injI)
  apply transfer
  apply (auto simp add: fun_eq_iff)
  done

lemma bit_seq_of_nat_cset_bij: "bij bit_seq_of_nat_set"
  apply (rule bijI)
   apply (fact bit_seq_of_nat_set_inj)
  apply transfer
  apply (rule surjI)
  apply auto
  done

text \<open> This function is a partial injection from countable sets of natural sets to natural sets.
        When used with the Schroeder-Bernstein theorem, it can be used to conjure a total
        bijection between these two types. \<close>

definition nat_set_cset_collapse :: "nat set cset \<Rightarrow> nat set" where
"nat_set_cset_collapse = inv bit_seq_of_nat_set \<circ> seq_inj \<circ> cset2seq \<circ> (\<lambda> A. (bit_seq_of_nat_set `\<^sub>c A))"

lemma nat_set_cset_collapse_inj: "inj_on nat_set_cset_collapse {A. A \<noteq> {}\<^sub>c}"
proof -
  have "(`\<^sub>c) bit_seq_of_nat_set ` {A. A \<noteq> {}\<^sub>c} \<subseteq> {A. A \<noteq> {}\<^sub>c}"
    by (auto simp add:cimage.rep_eq)
  thus ?thesis
    apply (simp add: nat_set_cset_collapse_def)
    apply (rule comp_inj_on)
     apply (meson bit_seq_of_nat_set_inj cset.inj_map injD inj_onI)
    apply (rule comp_inj_on)
     apply (metis cset2seq_inj subset_inj_on)
    apply (rule comp_inj_on)
     apply (rule subset_inj_on)
      apply (rule seq_inj)
     apply (simp)
    apply (meson UNIV_I bij_imp_bij_inv bij_is_inj bit_seq_of_nat_cset_bij subsetI subset_inj_on)
    done
qed

lemma inj_csingle:
  "inj csingle"
  by (auto intro: injI simp add: cinsert_def bot_cset.rep_eq)

lemma range_csingle:
  "range csingle \<subseteq> {A. A \<noteq> {}\<^sub>c}"
  by (auto)

lift_definition csets :: "'a set \<Rightarrow> 'a cset set" is
"\<lambda> A. {B. B \<subseteq> A \<and> countable B}" by auto

lemma csets_finite: "finite A \<Longrightarrow> finite (csets A)"
  by (auto simp add: csets_def)

lemma csets_infinite: "infinite A \<Longrightarrow> infinite (csets A)"
  by (auto simp add: csets_def, metis csets.abs_eq csets.rep_eq finite_countable_subset finite_imageI)

lemma csets_UNIV:
  "csets (UNIV :: 'a set) = (UNIV :: 'a cset set)"
  by (auto simp add: csets_def, metis image_iff rcset rcset_inverse)

lemma infinite_nempty_cset:
  assumes "infinite (UNIV :: 'a set)"
  shows "infinite ({A. A \<noteq> {}\<^sub>c} :: 'a cset set)"
proof -
  have "infinite (UNIV :: 'a cset set)"
    by (metis assms csets_UNIV csets_infinite)
  hence "infinite ((UNIV :: 'a cset set) - {{}\<^sub>c})"
    by (rule infinite_remove)
  thus ?thesis
    by (auto)
qed

lemma nat_set_cset_partial_bij:
  obtains f :: "nat set cset \<Rightarrow> nat set" where "bij_betw f {A. A \<noteq> {}\<^sub>c} UNIV"
  using Schroeder_Bernstein[OF nat_set_cset_collapse_inj, of UNIV csingle, simplified, OF inj_csingle range_csingle]
  by (auto)

lemma nat_set_cset_bij:
  obtains f :: "nat set cset \<Rightarrow> nat set" where "bij f"
proof -
  obtain g :: "nat set cset \<Rightarrow> nat set" where "bij_betw g {A. A \<noteq> {}\<^sub>c} UNIV"
    using nat_set_cset_partial_bij by blast
  moreover obtain h :: "nat set cset \<Rightarrow> nat set cset" where "bij_betw h UNIV {A. A \<noteq> {}\<^sub>c}"
  proof -
    have "infinite (UNIV :: nat set cset set)"
      by (metis Finite_Set.finite_set csets_UNIV csets_infinite infinite_UNIV_char_0)
    then obtain h' :: "nat set cset \<Rightarrow> nat set cset" where "bij_betw h' UNIV (UNIV - {{}\<^sub>c})"
      using infinite_imp_bij_betw[of "UNIV :: nat set cset set" "{}\<^sub>c"] by auto
    moreover have "(UNIV :: nat set cset set) - {{}\<^sub>c} = {A. A \<noteq> {}\<^sub>c}"
      by (auto)
    ultimately show ?thesis
      using that by (auto)
  qed
  ultimately have "bij (g \<circ> h)"
    using bij_betw_trans by blast
  with that show ?thesis
    by (auto)
qed

definition "nat_set_cset_bij = (SOME f :: nat set cset \<Rightarrow> nat set. bij f)"

lemma bij_nat_set_cset_bij:
  "bij nat_set_cset_bij"
  by (metis nat_set_cset_bij nat_set_cset_bij_def someI_ex)

lemma inj_on_image_csets:
  "inj_on f A \<Longrightarrow> inj_on ((`\<^sub>c) f) (csets A)"
  by (fastforce simp add: inj_on_def cimage_def cin_def csets_def)

lemma image_csets_surj:
  "\<lbrakk> inj_on f A; f ` A = B \<rbrakk> \<Longrightarrow> (`\<^sub>c) f ` csets A = csets B"
  apply (auto simp add: cimage_def csets_def image_mono map_fun_def)
  apply (simp add: image_comp)
  apply (auto simp add: image_Collect)
  apply (erule subset_imageE)
  using countable_image_inj_on subset_inj_on by blast

lemma bij_betw_image_csets:
  "bij_betw f A B \<Longrightarrow> bij_betw ((`\<^sub>c) f) (csets A) (csets B)"
  by (simp add: bij_betw_def inj_on_image_csets image_csets_surj)
end