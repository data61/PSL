section \<open> Symmetric Lenses \<close>

theory Lens_Symmetric
  imports Lens_Order
begin

text \<open> A characterisation of Hofmann's ``Symmetric Lenses''~\cite{Hofmann2011}, where
  a lens is accompanied by its complement. \<close>

record ('a, 'b, 's) slens = 
  view   :: "'a \<Longrightarrow> 's" ("\<V>\<index>") \<comment> \<open> The region characterised \<close>
  coview :: "'b \<Longrightarrow> 's" ("\<C>\<index>") \<comment> \<open> The complement of the region \<close>

type_notation
  slens ("<_, _> \<Longleftrightarrow> _" [0, 0, 0] 0)

declare slens.defs [lens_defs]

definition slens_compl :: "(<'a, 'c> \<Longleftrightarrow> 'b) \<Rightarrow> <'c, 'a> \<Longleftrightarrow> 'b" ("-\<^sub>L _" [81] 80) where
[lens_defs]: "slens_compl a = \<lparr> view = coview a, coview = view a \<rparr>"

lemma view_slens_compl [simp]: "\<V>\<^bsub>-\<^sub>L a\<^esub> =  \<C>\<^bsub>a\<^esub>"
  by (simp add: slens_compl_def)

lemma coview_slens_compl [simp]: "\<C>\<^bsub>-\<^sub>L a\<^esub> =  \<V>\<^bsub>a\<^esub>"
  by (simp add: slens_compl_def)

subsection \<open> Partial Symmetric Lenses \<close>

locale psym_lens =
  fixes S :: "<'a, 'b> \<Longleftrightarrow> 's" (structure)
  assumes 
    mwb_region [simp]: "mwb_lens \<V>" and
    mwb_coregion [simp]: "mwb_lens \<C>" and
    indep_region_coregion [simp]: "\<V> \<bowtie> \<C>" and
    pbij_region_coregion [simp]: "pbij_lens (\<V> +\<^sub>L \<C>)"

declare psym_lens.mwb_region [simp]
declare psym_lens.mwb_coregion [simp]
declare psym_lens.indep_region_coregion [simp]

lemma psym_lens_compl [simp]: "psym_lens a \<Longrightarrow> psym_lens (-\<^sub>L a)"
  apply (simp add: slens_compl_def)
  apply (rule psym_lens.intro)
  apply (simp_all)
  using lens_indep_sym psym_lens.indep_region_coregion apply blast
  using lens_indep_sym pbij_plus_commute psym_lens_def apply blast
  done

subsection \<open> Symmetric Lenses \<close>

locale sym_lens =
  fixes S :: "<'a, 'b> \<Longleftrightarrow> 's" (structure)
  assumes 
    vwb_region: "vwb_lens \<V>" and
    vwb_coregion: "vwb_lens \<C>" and
    indep_region_coregion: "\<V> \<bowtie> \<C>" and
    bij_region_coregion: "bij_lens (\<V> +\<^sub>L \<C>)"
begin

sublocale psym_lens
proof (rule psym_lens.intro)
  show "mwb_lens \<V>"
    by (simp add: vwb_region)
  show "mwb_lens \<C>"
    by (simp add: vwb_coregion)
  show "\<V> \<bowtie> \<C>"
    using indep_region_coregion by blast
  show "pbij_lens (\<V> +\<^sub>L \<C>)"
    by (simp add: bij_region_coregion)
qed

lemma put_region_coregion_cover:
  "put\<^bsub>\<V>\<^esub> (put\<^bsub>\<C>\<^esub> s\<^sub>1 (get\<^bsub>\<C>\<^esub> s\<^sub>2)) (get\<^bsub>\<V>\<^esub> s\<^sub>2) = s\<^sub>2"
proof -
  have "put\<^bsub>\<V>\<^esub> (put\<^bsub>\<C>\<^esub> s\<^sub>1 (get\<^bsub>\<C>\<^esub> s\<^sub>2)) (get\<^bsub>\<V>\<^esub> s\<^sub>2) = put\<^bsub>\<V> +\<^sub>L \<C>\<^esub> s\<^sub>1 (get\<^bsub>\<V> +\<^sub>L \<C>\<^esub> s\<^sub>2)"
    by (simp add: lens_defs)
  also have "... = s\<^sub>2"
    by (simp add: bij_region_coregion)
  finally show ?thesis .
qed

end

declare sym_lens.vwb_region [simp]
declare sym_lens.vwb_coregion [simp]
declare sym_lens.indep_region_coregion [simp]

lemma sym_lens_psym [simp]: "sym_lens x \<Longrightarrow> psym_lens x"
  by (simp add: psym_lens_def sym_lens.bij_region_coregion)

lemma sym_lens_compl [simp]: "sym_lens a \<Longrightarrow> sym_lens (-\<^sub>L a)"
  apply (simp add: slens_compl_def)
  apply (rule sym_lens.intro, simp_all)
  using lens_indep_sym sym_lens.indep_region_coregion apply blast
  using bij_lens_equiv lens_plus_comm sym_lens_def apply blast
  done

end