theory Case_Labeling
imports Main
keywords "print_nested_cases" :: diag
begin

section \<open>Labeling Subgoals\<close>

context begin
  qualified type_synonym prg_ctxt_var = unit
  qualified type_synonym prg_ctxt = "string \<times> nat \<times> prg_ctxt_var list"

  text \<open>Embed variables in terms\<close>
  qualified definition VAR :: "'v \<Rightarrow> prg_ctxt_var" where
    "VAR _ = ()"

  text \<open>Labeling of a subgoal\<close>
  qualified definition VC :: "prg_ctxt list \<Rightarrow> 'a \<Rightarrow> 'a" where
    "VC ct P \<equiv> P"

  text \<open>Computing the statement numbers and context\<close>
  qualified definition CTXT :: "nat \<Rightarrow> prg_ctxt list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
    "CTXT inp ct outp P \<equiv> P"

  text \<open>Labeling of a term binding or assumption\<close>
  qualified definition BIND :: "string \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a" where
    "BIND name inp P \<equiv> P"

  text \<open>Hierarchy labeling\<close>
  qualified definition HIER :: "prg_ctxt list \<Rightarrow> 'a \<Rightarrow> 'a" where
    "HIER ct P \<equiv> P"

  text \<open>Split Labeling. This is used as an assumption\<close>
  qualified definition SPLIT :: "'a \<Rightarrow> 'a \<Rightarrow> bool" where
    "SPLIT v w \<equiv> v = w"

  text \<open>Disambiguation Labeling. This is used as an assumption\<close>
  qualified definition DISAMBIG :: "nat \<Rightarrow> bool" where
    "DISAMBIG n \<equiv> True"

  lemmas LABEL_simps = BIND_def CTXT_def HIER_def SPLIT_def VC_def

  lemma Initial_Label: "CTXT 0 [] outp P \<Longrightarrow> P"
    by (simp add: Case_Labeling.CTXT_def)

  lemma
    BIND_I: "P \<Longrightarrow> BIND name inp P" and
    BIND_D: "BIND name inp P \<Longrightarrow> P" and
    VC_I: "P \<Longrightarrow> VC ct P"
    unfolding Case_Labeling.BIND_def Case_Labeling.VC_def .

  lemma DISAMBIG_I: "(DISAMBIG n \<Longrightarrow> P) \<Longrightarrow> P"
    by (auto simp: DISAMBIG_def Case_Labeling.VC_def)

  lemma DISAMBIG_E: "(DISAMBIG n \<Longrightarrow> P) \<Longrightarrow> P"
    by (auto simp: DISAMBIG_def)

  text \<open>Lemmas for the tuple postprocessing\<close>
  lemma SPLIT_reflection: "SPLIT x y \<Longrightarrow> (x \<equiv> y)"
    unfolding SPLIT_def by (rule eq_reflection)

  lemma rev_SPLIT_reflection: "(x \<equiv> y) \<Longrightarrow> SPLIT x y"
    unfolding SPLIT_def ..

  lemma SPLIT_sym: "SPLIT x y \<Longrightarrow> SPLIT y x"
    unfolding SPLIT_def by (rule sym)

  lemma SPLIT_thin_refl: "\<lbrakk>SPLIT x x; PROP W\<rbrakk> \<Longrightarrow> PROP W" .

  lemma SPLIT_subst: "\<lbrakk>SPLIT x y; P x\<rbrakk> \<Longrightarrow> P y"
    unfolding SPLIT_def by hypsubst

  lemma SPLIT_prodE:
    assumes "SPLIT (x1, y1) (x2, y2)"
    obtains "SPLIT x1 x2" "SPLIT y1 y2"
    using assms unfolding SPLIT_def by auto


end

text \<open>
  The labeling constants were qualified to not interfere with any other theory.
  The following locale allows using a nice syntax in other theories
\<close>

locale Labeling_Syntax begin
  abbreviation VAR where "VAR \<equiv> Case_Labeling.VAR"
  abbreviation VC ("V\<langle>(2_,_:/ _)\<rangle>") where "VC bl ct  \<equiv> Case_Labeling.VC (bl # ct)"
  abbreviation CTXT ("C\<langle>(2_,_,_:/ _\<rangle>)") where "CTXT \<equiv> Case_Labeling.CTXT"
  abbreviation BIND ("B\<langle>(2_,_:/ _\<rangle>)") where "BIND \<equiv> Case_Labeling.BIND"
  abbreviation HIER ("H\<langle>(2_:/ _\<rangle>)") where "HIER \<equiv> Case_Labeling.HIER"
  abbreviation SPLIT where "SPLIT \<equiv> Case_Labeling.SPLIT"
end

text \<open>Lemmas for converting terms from @{term Suc}/@{term "0::nat"} notation to numerals\<close>
lemma Suc_numerals_conv:
  "Suc 0 = Numeral1"
  "Suc (numeral n) = numeral (n + num.One)"
  by auto

lemmas Suc_numeral_simps = Suc_numerals_conv add_num_simps


section \<open>Casify\<close>

text \<open>
  Introduces a command @{command print_nested_cases}. This is similar to @{command print_cases},
  but shows also the nested cases.
\<close>
ML_file \<open>print_nested_cases.ML\<close>

ML_file \<open>util.ML\<close>

text \<open>Introduces the proof method.\<close>
ML_file \<open>casify.ML\<close>


ML \<open>
  val casify_defs = Casify.Options { simp_all_cases=true, split_right_only=true, protect_subgoals=false }
\<close>

method_setup prepare_labels = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (ALLGOALS (Casify.prepare_labels_tac ctxt)))
\<close> "VCG labelling: prepare labels"

method_setup casify = \<open>Casify.casify_method_setup casify_defs\<close>
  "VCG labelling: Turn the labels into cases"

end
