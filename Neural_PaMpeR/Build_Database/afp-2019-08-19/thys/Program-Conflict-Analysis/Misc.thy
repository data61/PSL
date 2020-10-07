(*  Title:       Miscellanneous Definitions and Lemmas
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)

section \<open>Miscellanneous Definitions and Lemmas\<close>

theory Misc
imports Main "HOL-Library.Multiset" "HOL-Library.Subseq_Order"
begin
text_raw \<open>\label{thy:Misc}\<close>

text \<open>Here we provide a collection of miscellaneous definitions and helper lemmas\<close>

subsection "Miscellanneous (1)"
text \<open>This stuff is used in this theory itself, and thus occurs in first place. There is another ,,Miscellaneous''-section at the end of this theory\<close>
subsubsection "AC-operators"
  
text \<open>Locale to declare AC-laws as simplification rules\<close>
locale AC =
  fixes f
  assumes commute[simp]: "f x y = f y x"
  assumes assoc[simp]: "f (f x y) z = f x (f y z)"

lemma (in AC) left_commute[simp]: "f x (f y z) = f y (f x z)"
  by (simp only: assoc[symmetric]) simp

text \<open>Locale to define functions from surjective, unique relations\<close>
locale su_rel_fun =
  fixes F and f
  assumes unique: "\<lbrakk>(A,B)\<in>F; (A,B')\<in>F\<rbrakk> \<Longrightarrow> B=B'"
  assumes surjective: "\<lbrakk>!!B. (A,B)\<in>F \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  assumes f_def: "f A == THE B. (A,B)\<in>F"

lemma (in su_rel_fun) repr1: "(A,f A)\<in>F" proof (unfold f_def)
  obtain B where "(A,B)\<in>F" by (rule surjective)
  with theI[where P="\<lambda>B. (A,B)\<in>F", OF this] show "(A, THE x. (A, x) \<in> F) \<in> F" by (blast intro: unique)
qed
  
lemma (in su_rel_fun) repr2: "(A,B)\<in>F \<Longrightarrow> B=f A" using repr1
  by (blast intro: unique)

lemma (in su_rel_fun) repr: "(f A = B) = ((A,B)\<in>F)" using repr1 repr2
  by (blast) 


subsection \<open>Abbreviations for list order\<close>

abbreviation ileq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infix "\<preceq>" 50) where
  "(\<preceq>) \<equiv> (\<le>)"

abbreviation ilt :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool"  (infix "\<prec>" 50) where
  "(\<prec>) \<equiv> (<)"


subsection \<open>Multisets\<close>

(*
  The following is a syntax extension for multisets. Unfortunately, it depends on a change in the Library/Multiset.thy, so it is commented out here, until it will be incorporated 
  into Library/Multiset.thy by its maintainers.

  The required change in Library/Multiset.thy is removing the syntax for single:
     - single :: "'a => 'a multiset"    ("{#_#}")
     + single :: "'a => 'a multiset"

  And adding the following translations instead:
  
     + syntax
     + "_multiset" :: "args \<Rightarrow> 'a multiset" ("{#(_)#}")

     + translations
     +   "{#x, xs#}" == "{#x#} + {#xs#}" 
     +   "{# x #}" == "single x"

  This translates "{# \<dots> #}" into a sum of singletons, that is parenthesized to the right. ?? Can we also achieve left-parenthesizing ??

*)


  (* Let's try what happens if declaring AC-rules for multiset union as simp-rules *)
(*declare union_ac[simp] -- don't do it !*)

subsubsection \<open>Case distinction\<close>

lemma multiset_induct'[case_names empty add]: "\<lbrakk>P {#}; \<And>M x. P M \<Longrightarrow> P ({#x#}+M)\<rbrakk> \<Longrightarrow> P M"
  by (induct rule: multiset_induct) (auto simp add: union_commute)

subsubsection \<open>Count\<close>
  lemma count_ne_remove: "\<lbrakk> x ~= t\<rbrakk> \<Longrightarrow> count S x = count (S-{#t#}) x"
    by (auto)
  lemma mset_empty_count[simp]: "(\<forall>p. count M p = 0) = (M={#})"
    by (auto simp add: multiset_eq_iff)

subsubsection \<open>Union, difference and intersection\<close>

  lemma size_diff_se: "\<lbrakk>t \<in># S\<rbrakk> \<Longrightarrow> size S = size (S - {#t#}) + 1" proof (unfold size_multiset_overloaded_eq)
    let ?SIZE = "sum (count S) (set_mset S)"
    assume A: "t \<in># S"
    from A have SPLITPRE: "finite (set_mset S) & {t}\<subseteq>(set_mset S)" by auto
    hence "?SIZE = sum (count S) (set_mset S - {t}) + sum (count S) {t}" by (blast dest: sum.subset_diff)
    hence "?SIZE = sum (count S) (set_mset S - {t}) + count (S) t" by auto
    moreover with A have "count S t = count (S-{#t#}) t + 1" by auto
    ultimately have D: "?SIZE = sum (count S) (set_mset S - {t}) + count (S-{#t#}) t + 1" by (arith)
    moreover have "sum (count S) (set_mset S - {t}) = sum (count (S-{#t#})) (set_mset S - {t})" proof -
      have "ALL x:(set_mset S - {t}) . count S x = count (S-{#t#}) x" by (auto iff add: count_ne_remove)
      thus ?thesis by simp
    qed
    ultimately have D: "?SIZE = sum (count (S-{#t#})) (set_mset S - {t}) + count (S-{#t#}) t + 1" by (simp)
    moreover
    { assume CASE: "t \<notin># S - {#t#}"
      from CASE have "set_mset S - {t} = set_mset (S - {#t#})"
        by (simp add: at_most_one_mset_mset_diff)
      with CASE D have "?SIZE = sum (count (S-{#t#})) (set_mset (S - {#t#})) + 1"
        by (simp add: not_in_iff)
    }
    moreover
    { assume CASE: "t \<in># S - {#t#}"
      from CASE have 1: "set_mset S = set_mset (S-{#t#})"
        by (rule more_than_one_mset_mset_diff [symmetric])
      moreover from D have "?SIZE = sum (count (S-{#t#})) (set_mset S - {t}) + sum (count (S-{#t#})) {t} + 1" by simp
      moreover from SPLITPRE sum.subset_diff have "sum (count (S-{#t#})) (set_mset S) = sum (count (S-{#t#})) (set_mset S - {t}) + sum (count (S-{#t#})) {t}" by (blast)
      ultimately have "?SIZE = sum (count (S-{#t#})) (set_mset (S-{#t#})) + 1" by simp
    }
    ultimately show "?SIZE = sum (count (S-{#t#})) (set_mset (S - {#t#})) + 1" by blast
  qed

  (* TODO: Check whether this proof can be done simpler *)
  lemma mset_union_diff_comm: "t \<in># S \<Longrightarrow> T + (S - {#t#}) = (T + S) - {#t#}" proof -
    assume "t \<in># S"
    then obtain S' where S: "S = add_mset t S'"
      by (metis insert_DiffM)
    then show ?thesis
      by auto
  qed

  lemma mset_right_cancel_union: "\<lbrakk>a \<in># A+B; ~(a \<in># B)\<rbrakk> \<Longrightarrow> a\<in>#A"
    by (simp)
  lemma mset_left_cancel_union: "\<lbrakk>a \<in># A+B; ~(a \<in># A)\<rbrakk> \<Longrightarrow> a\<in>#B"
    by (simp)
  
  lemmas mset_cancel_union = mset_right_cancel_union mset_left_cancel_union

  lemma mset_right_cancel_elem: "\<lbrakk>a \<in># A+{#b#}; a~=b\<rbrakk> \<Longrightarrow> a\<in>#A"
    apply(subgoal_tac "~(a \<in># {#b#})")
    apply(auto)
  done

  lemma mset_left_cancel_elem: "\<lbrakk>a \<in># {#b#}+A; a~=b\<rbrakk> \<Longrightarrow> a\<in>#A"
    apply(subgoal_tac "~(a \<in># {#b#})")
    apply(auto)
  done

  lemmas mset_cancel_elem = mset_right_cancel_elem mset_left_cancel_elem

  lemma mset_diff_cancel1elem[simp]: "~(a \<in># B) \<Longrightarrow> {#a#}-B = {#a#}" proof -
    assume A: "~(a \<in># B)"
    hence "count ({#a#}-B) a = count ({#a#}) a" by (auto simp add: not_in_iff)
    moreover have "ALL e . e~=a \<longrightarrow> count ({#a#}-B) e = count ({#a#}) e" by auto
    ultimately show ?thesis by (auto simp add: multiset_eq_iff)
  qed

  (*lemma union_diff_assoc_se: "t \<in># B \<Longrightarrow> (A+B)-{#t#} = A + (B-{#t#})"
    by (auto iff add: multiset_eq_iff)
  lemma union_diff_assoc_se2: "t \<in># A \<Longrightarrow> (A+B)-{#t#} = (A-{#t#}) + B"
    by (auto iff add: multiset_eq_iff)
  lemmas union_diff_assoc_se = union_diff_assoc_se1 union_diff_assoc_se2*)

  lemma union_diff_assoc: "C-B={#} \<Longrightarrow> (A+B)-C = A + (B-C)"
    by (simp add: multiset_eq_iff)

  lemma mset_union_2_elem: "{#a#}+{#b#} = M + {#c#} \<Longrightarrow> {#a#}=M & b=c | a=c & {#b#}=M"
    by (auto simp: add_eq_conv_diff)

  lemma mset_un_cases[cases set, case_names left right]:
    "\<lbrakk>a \<in># A + B; a\<in>#A \<Longrightarrow> P; a\<in>#B \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    by (auto)

  lemma mset_unplusm_dist_cases[cases set, case_names left right]:
    assumes A: "add_mset s A = B+C"
    assumes L: "\<lbrakk>B=add_mset s (B-{#s#}); A=(B-{#s#})+C\<rbrakk> \<Longrightarrow> P"
    assumes R: "\<lbrakk>C=add_mset s (C-{#s#}); A=B+(C-{#s#})\<rbrakk> \<Longrightarrow> P" 
    shows P
  proof -
    from A[symmetric] have "s \<in># B+C" by simp
    thus ?thesis proof (cases rule: mset_un_cases)
      case left hence 1: "B=add_mset s (B-{#s#})" by simp
      with A have "add_mset s A = add_mset s ((B-{#s#})+C)" by (simp add: union_ac)
      hence 2: "A = (B-{#s#})+C" by (simp)
      from L[OF 1 2] show ?thesis .
    next
      case right hence 1: "C=add_mset s (C-{#s#})" by simp
      with A have "add_mset s A = add_mset s (B+(C-{#s#}))" by (simp add: union_ac)
      hence 2: "A = B+(C-{#s#})" by (simp)
      from R[OF 1 2] show ?thesis .
    qed
  qed

  lemma mset_unplusm_dist_cases2[cases set, case_names left right]:
    assumes A: "B+C = add_mset s A"
    assumes L: "\<lbrakk>B=add_mset s (B-{#s#}); A=(B-{#s#})+C\<rbrakk> \<Longrightarrow> P"
    assumes R: "\<lbrakk>C=add_mset s (C-{#s#}); A=B+(C-{#s#})\<rbrakk> \<Longrightarrow> P" 
    shows P
    using mset_unplusm_dist_cases[OF A[symmetric]] L R by blast

  lemma mset_single_cases[cases set, case_names loc env]: 
    assumes A: "add_mset s c = add_mset r' c'" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "\<lbrakk>c'={#s#}+(c'-{#s#}); c={#r'#}+(c-{#r'#}); c-{#r'#} = c'-{#s#} \<rbrakk> \<Longrightarrow> P" 
    shows "P"
  proof -
    { assume CASE: "s=r'"
      with A have "c=c'" by simp
      with CASE CASES have ?thesis by auto
    } moreover {
      assume CASE: "s\<noteq>r'"
      have "s\<in>#{#s#}+c" by simp
      with A have "s \<in># {#r'#} + c'" by simp
      with CASE have "s \<in># c'" 
        by simp
      from insert_DiffM[OF this, symmetric] have 1: "c' = add_mset s (c' - {#s#})" .
      with A have "{#s#}+c = {#s#}+({#r'#}+(c' - {#s#}))" by (auto simp add: union_ac)
      hence 2: "c={#r'#}+(c' - {#s#})" by (auto)
      hence 3: "c-{#r'#} = (c' - {#s#})" by auto
      from 1 2 3 CASES have ?thesis by auto
    } ultimately show ?thesis by blast
  qed

  lemma mset_single_cases'[cases set, case_names loc env]: 
    assumes A: "add_mset s c = add_mset r' c'" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "!!cc. \<lbrakk>c'={#s#}+cc; c={#r'#}+cc; c'-{#s#}=cc; c-{#r'#}=cc\<rbrakk> \<Longrightarrow> P" 
    shows "P"
    using A  CASES by (auto elim!: mset_single_cases)

  lemma mset_single_cases2[cases set, case_names loc env]: 
    assumes A: "add_mset s c = add_mset r' c'" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "\<lbrakk>c'=(c'-{#s#})+{#s#}; c=(c-{#r'#})+{#r'#}; c-{#r'#} = c'-{#s#} \<rbrakk> \<Longrightarrow> P" 
    shows "P" 
  proof -
    from A have "add_mset s c = add_mset r' c'" by simp
    thus ?thesis proof (cases rule: mset_single_cases)
      case loc with CASES show ?thesis by simp
    next
      case env with CASES show ?thesis by (simp add: union_ac)
    qed
  qed

  lemma mset_single_cases2'[cases set, case_names loc env]: 
    assumes A: "add_mset s c = add_mset r' c'" 
    assumes CASES: "\<lbrakk>s=r'; c=c'\<rbrakk> \<Longrightarrow> P" "!!cc. \<lbrakk>c'=cc+{#s#}; c=cc+{#r'#}; c'-{#s#}=cc; c-{#r'#}=cc\<rbrakk> \<Longrightarrow> P" 
    shows "P"
    using A  CASES by (auto elim!: mset_single_cases2)

  lemma mset_un_single_un_cases [consumes 1, case_names left right]:
    assumes A: "add_mset a A = B + C"
      and CASES: "a \<in># B \<Longrightarrow> A = (B - {#a#}) + C \<Longrightarrow> P"
        "a \<in># C \<Longrightarrow> A = B + (C - {#a#}) \<Longrightarrow> P"
    shows P
  proof -
    have "a \<in># A+{#a#}" by simp
    with A have "a \<in># B+C" by auto
    thus ?thesis proof (cases rule: mset_un_cases)
      case left hence "B=B-{#a#}+{#a#}" by auto
      with A have "A+{#a#} = (B-{#a#})+C+{#a#}" by (auto simp add: union_ac)
      hence "A=(B-{#a#})+C" by simp
      with CASES(1)[OF left] show ?thesis by blast
    next
      case right hence "C=C-{#a#}+{#a#}" by auto
      with A have "A+{#a#} = B+(C-{#a#})+{#a#}" by (auto simp add: union_ac)
      hence "A=B+(C-{#a#})" by simp
      with CASES(2)[OF right] show ?thesis by blast
    qed
  qed

      (* TODO: Can this proof be done more automatically ? *)
  lemma mset_distrib[consumes 1, case_names dist]: assumes A: "(A::'a multiset)+B = M+N" "!!Am An Bm Bn. \<lbrakk>A=Am+An; B=Bm+Bn; M=Am+Bm; N=An+Bn\<rbrakk> \<Longrightarrow> P" shows "P"
  proof -
    have BN_MA: "B - N = M - A"
      by (metis (no_types) add_diff_cancel_right assms(1) union_commute)
    have H: "A = A\<inter># C + (A - C) \<inter># D" if "A + B = C + D" for A B C D :: "'a multiset"
      by (metis add.commute diff_intersect_left_idem mset_subset_eq_add_left subset_eq_diff_conv
          subset_mset.add_diff_inverse subset_mset.inf_absorb1 subset_mset.inf_le1 that)
    have A': "A = A\<inter># M + (A - M) \<inter># N"
      using A(1) H by blast
    moreover have B': "B = (B - N) \<inter># M + B\<inter># N"
      using A(1) H[of B A N M] by (auto simp: ac_simps)
    moreover have "M = A \<inter># M + (B - N) \<inter># M"
      using H[of M N A B] BN_MA[symmetric] A(1) by (metis (no_types) diff_intersect_left_idem
          diff_union_cancelR multiset_inter_commute subset_mset.diff_add subset_mset.inf.cobounded1
          union_commute)
    moreover have "N = (A - M) \<inter># N + B \<inter># N"
      by (metis A' assms(1) diff_union_cancelL inter_union_distrib_left inter_union_distrib_right
          mset_subset_eq_multiset_union_diff_commute subset_mset.inf.cobounded1 subset_mset.inf.commute)
    ultimately show P
      using A(2) by blast
  qed


subsubsection \<open>Singleton multisets\<close>   

lemma mset_size_le1_cases[case_names empty singleton,consumes 1]: "\<lbrakk> size M \<le> Suc 0; M={#} \<Longrightarrow> P; !!m. M={#m#} \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (cases M) auto

lemma diff_union_single_conv2:
  "a \<in># J \<Longrightarrow> J + I - {#a#} = (J - {#a#}) + I"
  using diff_union_single_conv [of a J I]
  by (simp add: union_ac)

lemmas diff_union_single_convs = diff_union_single_conv diff_union_single_conv2

lemma mset_contains_eq: "(m \<in># M) = ({#m#}+(M-{#m#})=M)" proof (auto)
  assume "add_mset m (M - {#m#}) = M"
  moreover have "m \<in># {#m#} + (M - {#m#})" by simp
  ultimately show "m \<in># M" by simp
qed


subsubsection \<open>Pointwise ordering\<close>

  lemma mset_le_incr_right1: "(a::'a multiset)\<subseteq>#b \<Longrightarrow> a\<subseteq>#b+c" using mset_subset_eq_mono_add[of a b "{#}" c, simplified] .
  lemma mset_le_incr_right2: "(a::'a multiset)\<subseteq>#b \<Longrightarrow> a\<subseteq>#c+b" using mset_le_incr_right1
    by (auto simp add: union_commute)
  lemmas mset_le_incr_right = mset_le_incr_right1 mset_le_incr_right2

  lemma mset_le_decr_left1: "(a::'a multiset)+c\<subseteq>#b \<Longrightarrow> a\<subseteq>#b" using mset_le_incr_right1 mset_subset_eq_mono_add_right_cancel
    by blast
  lemma mset_le_decr_left2: "c+(a::'a multiset)\<subseteq>#b \<Longrightarrow> a\<subseteq>#b" using mset_le_decr_left1
    by (auto simp add: union_ac)
  lemma mset_le_add_mset_decr_left1: "add_mset c a\<subseteq>#(b::'a multiset) \<Longrightarrow> a\<subseteq>#b"
    by (simp add: mset_subset_eq_insertD subset_mset.dual_order.strict_implies_order)
  lemma mset_le_add_mset_decr_left2: "add_mset c a\<subseteq>#(b::'a multiset) \<Longrightarrow> {#c#}\<subseteq>#b"
    by (simp add: mset_subset_eq_insertD subset_mset.dual_order.strict_implies_order)

  lemmas mset_le_decr_left = mset_le_decr_left1 mset_le_decr_left2 mset_le_add_mset_decr_left1
    mset_le_add_mset_decr_left2
  
  lemma mset_le_subtract: "(A::'a multiset)\<subseteq>#B \<Longrightarrow> A-C \<subseteq># B-C"
    apply (unfold subseteq_mset_def)
    apply auto
    apply (subgoal_tac "count A a \<le> count B a")
    apply arith
    apply simp
    done

  lemma mset_union_subset: "(A::'a multiset)+B \<subseteq># C \<Longrightarrow> A\<subseteq>#C \<and> B\<subseteq>#C"
    by (auto dest: mset_le_decr_left)
 
  lemma mset_le_add_mset: "add_mset x B \<subseteq># C \<Longrightarrow> {#x#}\<subseteq>#C \<and> B\<subseteq>#(C::'a multiset)"
    by (auto dest: mset_le_decr_left)
  
  lemma mset_le_subtract_left: "(A::'a multiset)+B \<subseteq># X \<Longrightarrow> B \<subseteq># X-A \<and> A\<subseteq>#X"
    by (auto dest: mset_le_subtract[of "A+B" "X" "A"] mset_union_subset)
  lemma mset_le_subtract_right: "(A::'a multiset)+B \<subseteq># X \<Longrightarrow> A \<subseteq># X-B \<and> B\<subseteq>#X"
    by (auto dest: mset_le_subtract[of "A+B" "X" "B"] mset_union_subset)

lemma mset_le_subtract_add_mset_left: "add_mset x B \<subseteq># (X::'a multiset) \<Longrightarrow> B \<subseteq># X-{#x#} \<and> {#x#}\<subseteq>#X"
    by (auto dest: mset_le_subtract[of "add_mset x B" "X" "{#x#}"] mset_le_add_mset)

  lemma mset_le_subtract_add_mset_right: "add_mset x B \<subseteq># (X::'a multiset) \<Longrightarrow> {#x#} \<subseteq># X-B \<and> B\<subseteq>#X"
    by (auto dest: mset_le_subtract[of "add_mset x B" "X" "B"] mset_le_add_mset)

  lemma mset_le_addE: "\<lbrakk> (xs::'a multiset) \<subseteq># ys; !!zs. ys=xs+zs \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P" using mset_subset_eq_exists_conv
    by blast

  declare subset_mset.diff_add[simp, intro]

  lemma mset_2dist2_cases:
    assumes A: "{#a, b#} \<subseteq># A + B"
    assumes CASES: "{#a, b#} \<subseteq># A \<Longrightarrow> P" "{#a, b#} \<subseteq># B \<Longrightarrow> P"
      "a \<in># A \<Longrightarrow> b \<in># B \<Longrightarrow> P" "a \<in># B \<Longrightarrow> b \<in># A \<Longrightarrow> P"
    shows "P"
  proof -
    from A have "count A a + count B a \<ge> 1"
      "count A b + count B b \<ge> 1"
      using mset_subset_eq_count [of "{#a, b#}" "A + B" a] mset_subset_eq_count [of "{#a, b#}" "A + B" b]
      by (auto split: if_splits)
    then have B: "a \<in># A \<or> a \<in># B"
      "b \<in># A \<or> b \<in># B"
      by (auto simp add: not_in_iff Suc_le_eq)
    { assume C: "a \<in># A" "b \<in># A - {#a#}" 
      with mset_subset_eq_mono_add [of "{#a#}" "{#a#}" "{#b#}" "A-{#a#}"]
      have "{#a, b#} \<subseteq># A" by (auto simp: add_mset_commute)
    } moreover {
      assume C: "a \<in># A" "b \<notin># A - {#a#}"
      with B A have "b \<in># B"
        by (auto simp: insert_subset_eq_iff diff_union_single_convs
            simp del: subset_mset.add_diff_assoc2)
    } moreover {
      assume C: "a \<notin># A" "b \<in># B - {#a#}"
      with A have "a \<in># B" using B by blast
      with C mset_subset_eq_mono_add [of "{#a#}" "{#a#}" "{#b#}" "B-{#a#}"]
      have "{#a, b#} \<subseteq># B" by (auto simp: add_mset_commute)
    } moreover {
      assume C: "a \<notin># A" "b \<notin># B - {#a#}"
      with A have "a \<in># B \<and> b \<in># A"
        apply (intro conjI)
         apply (auto dest!: mset_subset_eq_insertD simp: insert_union_subset_iff; fail)[]
        by (metis (no_types, lifting) B(1) add_mset_remove_trivial insert_DiffM2 
            mset_diff_cancel1elem single_subset_iff subset_eq_diff_conv subset_mset.diff_diff_right
            union_single_eq_member)
    } ultimately show P using CASES by blast
  qed

  lemma mset_union_subset_s: "{#a#}+B \<subseteq># C \<Longrightarrow> a \<in># C \<and> B \<subseteq># C"
    by (drule mset_union_subset) simp
  
  lemma mset_le_single_cases[consumes 1, case_names empty singleton]: "\<lbrakk>M\<subseteq>#{#a#}; M={#} \<Longrightarrow> P; M={#a#} \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
    by (induct M) auto
      
  lemma mset_le_distrib[consumes 1, case_names dist]: "\<lbrakk>X\<subseteq>#(A::'a multiset)+B; !!Xa Xb. \<lbrakk>X=Xa+Xb; Xa\<subseteq>#A; Xb\<subseteq>#B\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    by (auto elim!: mset_le_addE mset_distrib)

  lemma mset_le_mono_add_single: "\<lbrakk>a \<in># ys; b \<in># ws\<rbrakk> \<Longrightarrow> {#a, b#} \<subseteq># ys + ws" using mset_subset_eq_mono_add[of "{#a#}" _ "{#b#}", simplified] by (simp add: add_mset_commute)

  lemma mset_size1elem: "\<lbrakk>size P \<le> 1; q \<in># P\<rbrakk> \<Longrightarrow> P={#q#}"
    by (auto elim: mset_size_le1_cases)
  lemma mset_size2elem: "\<lbrakk>size P \<le> 2; {#q#}+{#q'#} \<subseteq># P\<rbrakk> \<Longrightarrow> P={#q#}+{#q'#}"
    by (auto elim: mset_le_addE)


subsubsection \<open>Image under function\<close>

notation image_mset (infixr "`#" 90)

lemma mset_map_single_rightE[consumes 1, case_names orig]: "\<lbrakk>f `# P = {#y#}; !!x. \<lbrakk> P={#x#}; f x = y \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  by (cases P) auto

lemma mset_map_split_orig: "!!M1 M2. \<lbrakk>f `# P = M1+M2; !!P1 P2. \<lbrakk>P=P1+P2; f `# P1 = M1; f `# P2 = M2\<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  apply (induct P)
  apply fastforce
  apply (force elim!: mset_un_single_un_cases simp add: union_ac) (* TODO: This proof need's quite long. Try to write a faster one. *)
  done

lemma mset_map_id: "\<lbrakk>!!x. f (g x) = x\<rbrakk> \<Longrightarrow> f `# g `# X = X"
  by (induct X) auto

text \<open>The following is a very specialized lemma. Intuitively, it splits the original multiset\<close>
text \<open>The following is a very specialized   by a splitting of some pointwise supermultiset of its image.

  Application:
  This lemma came in handy when proving the correctness of a constraint system that collects at most k sized submultisets of the sets of spawned threads.
\<close>
lemma mset_map_split_orig_le: assumes A: "f `# P \<subseteq># M1+M2" and EX: "!!P1 P2. \<lbrakk>P=P1+P2; f `# P1 \<subseteq># M1; f `# P2 \<subseteq># M2\<rbrakk> \<Longrightarrow> Q" shows "Q"
  using A EX by (auto elim: mset_le_distrib mset_map_split_orig)


subsection \<open>Lists\<close>

subsubsection \<open>Reverse lists\<close>
  lemma list_rev_decomp[rule_format]: "l~=[] \<longrightarrow> (EX ll e . l = ll@[e])"
    apply(induct_tac l)
    apply(auto)
  done
    
  (* Was already there as rev_induct
  lemma list_rev_induct: "\<lbrakk>P []; !! l e . P l \<Longrightarrow> P (l@[e]) \<rbrakk> \<Longrightarrow> P l"
    by (blast intro: rev_induct)
  proof (induct l rule: measure_induct[of length])
    fix x :: "'a list"
    assume A: "\<forall>y. length y < length x \<longrightarrow> P [] \<longrightarrow> (\<forall>x xa. P (x::'a list) \<longrightarrow> P (x @ [xa])) \<longrightarrow> P y" "P []" and IS: "\<And>l e. P l \<Longrightarrow> P (l @ [e])"
    show "P x" proof (cases "x=[]")
      assume "x=[]" with A show ?thesis by simp
    next
      assume CASE: "x~=[]"
      then obtain xx e where DECOMP: "x=xx@[e]" by (blast dest: list_rev_decomp)
      hence LEN: "length xx < length x" by auto
      with A IS have "P xx" by auto
      with IS have "P (xx@[e])" by auto
      with DECOMP show ?thesis by auto
    qed
  qed
  *)

  text \<open>Caution: Same order of case variables in snoc-case as @{thm [source] rev_exhaust}, the other way round than @{thm [source] rev_induct} !\<close>
  lemma length_compl_rev_induct[case_names Nil snoc]: "\<lbrakk>P []; !! l e . \<lbrakk>!! ll . length ll <= length l \<Longrightarrow> P ll\<rbrakk> \<Longrightarrow> P (l@[e])\<rbrakk> \<Longrightarrow> P l"
    apply(induct_tac l rule: length_induct)
    apply(case_tac "xs" rule: rev_cases)
    apply(auto)
  done

  lemma list_append_eq_Cons_cases: "\<lbrakk>ys@zs = x#xs; \<lbrakk>ys=[]; zs=x#xs\<rbrakk> \<Longrightarrow> P; !!ys'. \<lbrakk> ys=x#ys'; ys'@zs=xs \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    by (auto iff add: append_eq_Cons_conv)
  lemma list_Cons_eq_append_cases: "\<lbrakk>x#xs = ys@zs; \<lbrakk>ys=[]; zs=x#xs\<rbrakk> \<Longrightarrow> P; !!ys'. \<lbrakk> ys=x#ys'; ys'@zs=xs \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
    by (auto iff add: Cons_eq_append_conv)

subsubsection "folding"

text "Ugly lemma about foldl over associative operator with left and right neutral element"
lemma foldl_A1_eq: "!!i. \<lbrakk> !! e. f n e = e; !! e. f e n = e; !!a b c. f a (f b c) = f (f a b) c \<rbrakk> \<Longrightarrow> foldl f i ww = f i (foldl f n ww)"
proof (induct ww)
  case Nil thus ?case by simp
next
  case (Cons a ww i) note IHP[simplified]=this
  have "foldl f i (a # ww) = foldl f (f i a) ww" by simp
  also from IHP have "\<dots> = f (f i a) (foldl f n ww)" by blast
  also from IHP(4) have "\<dots> = f i (f a (foldl f n ww))" by simp
  also from IHP(1)[OF IHP(2,3,4), where i=a] have "\<dots> = f i (foldl f a ww)" by simp
  also from IHP(2)[of a] have "\<dots> = f i (foldl f (f n a) ww)" by simp
  also have "\<dots> = f i (foldl f n (a#ww))" by simp
  finally show ?case .
qed

lemmas foldl_conc_empty_eq = foldl_A1_eq[of "(@)" "[]", simplified]
lemmas foldl_un_empty_eq = foldl_A1_eq[of "(\<union>)" "{}", simplified, OF Un_assoc[symmetric]]

lemma foldl_set: "foldl (\<union>) {} l = \<Union>{x. x\<in>set l}"
  apply (induct l)
  apply simp_all
  apply (subst foldl_un_empty_eq)
  apply auto
  done


subsubsection \<open>Miscellaneous\<close>
  lemma length_compl_induct[case_names Nil Cons]: "\<lbrakk>P []; !! e l . \<lbrakk>!! ll . length ll <= length l \<Longrightarrow> P ll\<rbrakk> \<Longrightarrow> P (e#l)\<rbrakk> \<Longrightarrow> P l"
    apply(induct_tac l rule: length_induct)
    apply(case_tac "xs")
    apply(auto)
  done


  text \<open>Simultaneous induction over two lists, prepending an element to one of the lists in each step\<close>
  lemma list_2pre_induct[case_names base left right]: assumes BASE: "P [] []" and LEFT: "!!e w1' w2. P w1' w2 \<Longrightarrow> P (e#w1') w2" and RIGHT: "!!e w1 w2'. P w1 w2' \<Longrightarrow> P w1 (e#w2')" shows "P w1 w2" 
  proof -
    { \<comment> \<open>The proof is done by induction over the sum of the lengths of the lists\<close>
      fix n
      have "!!w1 w2. \<lbrakk>length w1 + length w2 = n; P [] []; !!e w1' w2. P w1' w2 \<Longrightarrow> P (e#w1') w2; !!e w1 w2'. P w1 w2' \<Longrightarrow> P w1 (e#w2') \<rbrakk> \<Longrightarrow> P w1 w2 " 
        apply (induct n)
        apply simp
        apply (case_tac w1)
        apply auto
        apply (case_tac w2)
        apply auto
        done
    } from this[OF _ BASE LEFT RIGHT] show ?thesis by blast
  qed


  lemma list_decomp_1: "length l=1 \<Longrightarrow> EX a . l=[a]"
    by (case_tac l, auto)

  lemma list_decomp_2: "length l=2 \<Longrightarrow> EX a b . l=[a,b]"
    by (case_tac l, auto simp add: list_decomp_1)


  lemma drop_all_conc: "drop (length a) (a@b) = b"
    by (simp)

  lemma list_rest_coinc: "\<lbrakk>length s2 <= length s1; s1@r1 = s2@r2\<rbrakk> \<Longrightarrow> EX r1p . r2=r1p@r1"
  proof -
    assume A: "length s2 <= length s1" "s1@r1 = s2@r2"
    hence "r1 = drop (length s1) (s2@r2)" by (auto simp only:drop_all_conc dest: sym)
    moreover from A have "length s1 = length s1 - length s2 + length s2" by arith
    ultimately have "r1 = drop ((length s1 - length s2)) r2" by (auto)
    hence "r2 = take ((length s1 - length s2)) r2 @ r1" by auto
    thus ?thesis by auto
  qed

  lemma list_tail_coinc: "n1#r1 = n2#r2 \<Longrightarrow> n1=n2 & r1=r2"
    by (auto)


  lemma last_in_set[intro]: "\<lbrakk>l\<noteq>[]\<rbrakk> \<Longrightarrow> last l \<in> set l"
    by (induct l) auto

subsection \<open>Induction on nat\<close>
  lemma nat_compl_induct[case_names 0 Suc]: "\<lbrakk>P 0; !! n . ALL nn . nn <= n \<longrightarrow> P nn \<Longrightarrow> P (Suc n)\<rbrakk> \<Longrightarrow> P n"
    apply(induct_tac n rule: nat_less_induct)
    apply(case_tac n)
    apply(auto)
  done


subsection \<open>Functions of type @{typ "bool\<Rightarrow>bool"}\<close>
  lemma boolfun_cases_helper: "g=(\<lambda>x. False) | g=(\<lambda>x. x) | g=(\<lambda>x. True) | g= (\<lambda>x. \<not>x)" 
  proof -
    { assume "g False" "g True"
      hence "g = (\<lambda>x. True)" by (rule_tac ext, case_tac x, auto)
    } moreover {
      assume "g False" "\<not>g True"
      hence "g = (\<lambda>x. \<not>x)" by (rule_tac ext, case_tac x, auto)
    } moreover {
      assume "\<not>g False" "g True"
      hence "g = (\<lambda>x. x)" by (rule_tac ext, case_tac x, auto)
    } moreover {
      assume "\<not>g False" "\<not>g True"
      hence "g = (\<lambda>x. False)" by (rule_tac ext, case_tac x, auto)
    } ultimately show ?thesis by fast
  qed

  lemma boolfun_cases[case_names False Id True Neg]: "\<lbrakk>g=(\<lambda>x. False) \<Longrightarrow> P g; g=(\<lambda>x. x) \<Longrightarrow> P g; g=(\<lambda>x. True) \<Longrightarrow> P g; g=(\<lambda>x. \<not>x) \<Longrightarrow> P g\<rbrakk> \<Longrightarrow> P g"
  proof -
    note boolfun_cases_helper[of g]
    moreover assume "g=(\<lambda>x. False) \<Longrightarrow> P g" "g=(\<lambda>x. x) \<Longrightarrow> P g" "g=(\<lambda>x. True) \<Longrightarrow> P g" "g=(\<lambda>x. \<not>x) \<Longrightarrow> P g"
    ultimately show ?thesis by fast
  qed


  subsection \<open>Definite and indefinite description\<close>
  text "Combined definite and indefinite description for binary predicate"
  lemma some_theI: assumes EX: "\<exists>a b . P a b" and BUN: "!! b1 b2 . \<lbrakk>\<exists>a . P a b1; \<exists>a . P a b2\<rbrakk> \<Longrightarrow> b1=b2" 
    shows "P (SOME a . \<exists>b . P a b) (THE b . \<exists>a . P a b)"
  proof -
    from EX have "EX b . P (SOME a . EX b . P a b) b" by (rule someI_ex)
    moreover from EX have "EX b . EX a . P a b" by blast
    with BUN theI'[of "\<lambda>b . EX a . P a b"] have "EX a . P a (THE b . EX a . P a b)" by (unfold Ex1_def, blast)
    moreover note BUN
    ultimately show ?thesis by (fast)
  qed
  


end
