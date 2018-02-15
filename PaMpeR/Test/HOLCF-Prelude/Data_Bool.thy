section \<open>Data: Bool\<close>

theory Data_Bool
  imports Type_Classes
begin

subsection \<open>Class instances\<close>

text \<open>Eq\<close>

lemma eq_eqI[case_names bottomLTR bottomRTL LTR RTL]:
  "(x = \<bottom> \<Longrightarrow> y = \<bottom>) \<Longrightarrow> (y = \<bottom> \<Longrightarrow> x = \<bottom>) \<Longrightarrow> (x = TT \<Longrightarrow> y = TT) \<Longrightarrow> (y = TT \<Longrightarrow> x = TT) \<Longrightarrow> x = y"
by (metis Exh_tr)

lemma eq_tr_simps [simp]:
  shows "eq\<cdot>TT\<cdot>TT = TT" and "eq\<cdot>TT\<cdot>FF = FF"
    and "eq\<cdot>FF\<cdot>TT = FF" and "eq\<cdot>FF\<cdot>FF = TT"
  unfolding TT_def FF_def eq_lift_def by simp_all

text \<open>Ord\<close>

lemma compare_tr_simps [simp]:
  "compare\<cdot>FF\<cdot>FF = EQ"
  "compare\<cdot>FF\<cdot>TT = LT"
  "compare\<cdot>TT\<cdot>FF = GT"
  "compare\<cdot>TT\<cdot>TT = EQ"
  unfolding TT_def FF_def compare_lift_def
  by simp_all

subsection \<open>Lemmas\<close>

lemma andalso_eq_TT_iff [simp]:
  "(x andalso y) = TT \<longleftrightarrow> x = TT \<and> y = TT"
  by (cases x, simp_all)

lemma andalso_eq_FF_iff [simp]:
  "(x andalso y) = FF \<longleftrightarrow> x = FF \<or> (x = TT \<and> y = FF)"
  by (cases x, simp_all)

lemma andalso_eq_bottom_iff [simp]:
  "(x andalso y) = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> (x = TT \<and> y = \<bottom>)"
  by (cases x, simp_all)

lemma orelse_eq_FF_iff [simp]:
  "(x orelse y) = FF \<longleftrightarrow> x = FF \<and> y = FF"
  by (cases x, simp_all)

lemma orelse_assoc [simp]:
  "((x orelse y) orelse z) = (x orelse y orelse z)"
  by (cases x) auto

lemma andalso_assoc [simp]:
  "((x andalso y) andalso z) = (x andalso y andalso z)"
  by (cases x) auto

lemma neg_orelse [simp]:
  "neg\<cdot>(x orelse y) = (neg\<cdot>x andalso neg\<cdot>y)"
  by (cases x) auto

lemma neg_andalso [simp]:
  "neg\<cdot>(x andalso y) = (neg\<cdot>x orelse neg\<cdot>y)"
  by (cases x) auto

text \<open>Not suitable as default simp rules, because they cause the
  simplifier to loop:\<close>
lemma neg_eq_simps:
  "neg\<cdot>x = TT \<Longrightarrow> x = FF"
  "neg\<cdot>x = FF \<Longrightarrow> x = TT"
  "neg\<cdot>x = \<bottom> \<Longrightarrow> x = \<bottom>"
  by (cases x, simp_all)+

lemma neg_eq_TT_iff [simp]: "neg\<cdot>x = TT \<longleftrightarrow> x = FF"
  by (cases x, simp_all)+

lemma neg_eq_FF_iff [simp]: "neg\<cdot>x = FF \<longleftrightarrow> x = TT"
  by (cases x, simp_all)+

lemma neg_eq_bottom_iff [simp]: "neg\<cdot>x = \<bottom> \<longleftrightarrow> x = \<bottom>"
  by (cases x, simp_all)+

(* TODO: set up reorient_proc for TT and FF *)

lemma neg_eq [simp]:
  "neg\<cdot>x = neg\<cdot>y \<longleftrightarrow> x = y"
  by (cases y, simp_all)

lemma neg_neg [simp]:
  "neg\<cdot>(neg\<cdot>x) = x"
  by (cases x, auto)

lemma neg_comp_neg [simp]:
  "neg oo neg = ID"
  by (metis cfun_eqI cfcomp2 neg_neg ID1)

end
