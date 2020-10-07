section \<open>Lens Algebraic Operators\<close>

theory Lens_Algebra
imports Lens_Laws
begin

subsection \<open>Lens Composition, Plus, Unit, and Identity\<close>

text \<open>
  \begin{figure}
  \begin{center}
    \includegraphics[width=7cm]{figures/Composition}
  \end{center}
  \vspace{-5ex}
  \caption{Lens Composition}
  \label{fig:Comp}
  \end{figure}
  We introduce the algebraic lens operators; for more information please see our paper~\cite{Foster16a}.
  Lens composition, illustrated in Figure~\ref{fig:Comp}, constructs a lens by composing the source 
  of one lens with the view of another.\<close>

definition lens_comp :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'c)" (infixr ";\<^sub>L" 80) where
[lens_defs]: "lens_comp Y X = \<lparr> lens_get = get\<^bsub>Y\<^esub> \<circ> lens_get X
                              , lens_put = (\<lambda> \<sigma> v. lens_put X \<sigma> (lens_put Y (lens_get X \<sigma>) v)) \<rparr>"

text \<open>
  \begin{figure}
  \begin{center}
    \includegraphics[width=7cm]{figures/Sum}
  \end{center}
  \vspace{-5ex}
  \caption{Lens Sum}
  \label{fig:Sum}
  \end{figure}
  Lens plus, as illustrated in Figure~\ref{fig:Sum} parallel composes two independent lenses, 
  resulting in a lens whose view is the product of the two underlying lens views.\<close>

definition lens_plus :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Longrightarrow> 'c" (infixr "+\<^sub>L" 75) where
[lens_defs]: "X +\<^sub>L Y = \<lparr> lens_get = (\<lambda> \<sigma>. (lens_get X \<sigma>, lens_get Y \<sigma>))
                       , lens_put = (\<lambda> \<sigma> (u, v). lens_put X (lens_put Y \<sigma> v) u) \<rparr>"

text \<open>The product functor lens similarly parallel composes two lenses, but in this case the lenses
  have different sources and so the resulting source is also a product.\<close>

definition lens_prod :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'd) \<Rightarrow> ('a \<times> 'b \<Longrightarrow> 'c \<times> 'd)" (infixr "\<times>\<^sub>L" 85) where
[lens_defs]: "lens_prod X Y = \<lparr> lens_get = map_prod get\<^bsub>X\<^esub> get\<^bsub>Y\<^esub>
                              , lens_put = \<lambda> (u, v) (x, y). (put\<^bsub>X\<^esub> u x, put\<^bsub>Y\<^esub> v y) \<rparr>"

text \<open>The $\lfst$ and $\lsnd$ lenses project the first and second elements, respectively, of a
  product source type.\<close>

definition fst_lens :: "'a \<Longrightarrow> 'a \<times> 'b" ("fst\<^sub>L") where
[lens_defs]: "fst\<^sub>L = \<lparr> lens_get = fst, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (u, \<rho>)) \<rparr>"

definition snd_lens :: "'b \<Longrightarrow> 'a \<times> 'b" ("snd\<^sub>L") where
[lens_defs]: "snd\<^sub>L = \<lparr> lens_get = snd, lens_put = (\<lambda> (\<sigma>, \<rho>) u. (\<sigma>, u)) \<rparr>"

lemma get_fst_lens [simp]: "get\<^bsub>fst\<^sub>L\<^esub> (x, y) = x"
  by (simp add: fst_lens_def)

lemma get_snd_lens [simp]: "get\<^bsub>snd\<^sub>L\<^esub> (x, y) = y"
  by (simp add: snd_lens_def)

text \<open>The swap lens is a bijective lens which swaps over the elements of the product source type.\<close>

abbreviation swap_lens :: "'a \<times> 'b \<Longrightarrow> 'b \<times> 'a" ("swap\<^sub>L") where
"swap\<^sub>L \<equiv> snd\<^sub>L +\<^sub>L fst\<^sub>L"

text \<open>The zero lens is an ineffectual lens whose view is a unit type. This means the zero lens
  cannot distinguish or change the source type.\<close>

definition zero_lens :: "unit \<Longrightarrow> 'a" ("0\<^sub>L") where
[lens_defs]: "0\<^sub>L = \<lparr> lens_get = (\<lambda> _. ()), lens_put = (\<lambda> \<sigma> x. \<sigma>) \<rparr>"

text \<open>The identity lens is a bijective lens where the source and view type are the same.\<close>

definition id_lens :: "'a \<Longrightarrow> 'a" ("1\<^sub>L") where
[lens_defs]: "1\<^sub>L = \<lparr> lens_get = id, lens_put = (\<lambda> _. id) \<rparr>"

text \<open>The quotient operator $X \lquot Y$ shortens lens $X$ by cutting off $Y$ from the end. It is
  thus the dual of the composition operator.\<close>

definition lens_quotient :: "('a \<Longrightarrow> 'c) \<Rightarrow> ('b \<Longrightarrow> 'c) \<Rightarrow> 'a \<Longrightarrow> 'b" (infixr "'/\<^sub>L" 90) where
[lens_defs]: "X /\<^sub>L Y = \<lparr> lens_get = \<lambda> \<sigma>. get\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>)
                       , lens_put = \<lambda> \<sigma> v. get\<^bsub>Y\<^esub> (put\<^bsub>X\<^esub> (create\<^bsub>Y\<^esub> \<sigma>) v) \<rparr>"

text \<open>Lens override uses a lens to replace part of a source type with a given value for the
  corresponding view.\<close>

definition lens_override :: "'a \<Rightarrow> 'a \<Rightarrow> ('b \<Longrightarrow> 'a) \<Rightarrow> 'a" ("_ \<oplus>\<^sub>L _ on _" [95,0,96] 95) where
[lens_defs]: "S\<^sub>1 \<oplus>\<^sub>L S\<^sub>2 on X = put\<^bsub>X\<^esub> S\<^sub>1 (get\<^bsub>X\<^esub> S\<^sub>2)"

text \<open>Lens inverse take a bijective lens and swaps the source and view types.\<close>

definition lens_inv :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('b \<Longrightarrow> 'a)" ("inv\<^sub>L") where
[lens_defs]: "lens_inv x = \<lparr> lens_get = create\<^bsub>x\<^esub>, lens_put = \<lambda> \<sigma>. get\<^bsub>x\<^esub> \<rparr>"

subsection \<open>Closure Poperties\<close>

text \<open>We show that the core lenses combinators defined above are closed under the key lens classes.\<close>
  
lemma id_wb_lens: "wb_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma source_id_lens: "\<S>\<^bsub>1\<^sub>L\<^esub> = UNIV"
  by (simp add: id_lens_def lens_source_def)

lemma unit_wb_lens: "wb_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: zero_lens_def)

lemma source_zero_lens: "\<S>\<^bsub>0\<^sub>L\<^esub> = UNIV"
  by (simp_all add: zero_lens_def lens_source_def)

lemma comp_weak_lens: "\<lbrakk> weak_lens x; weak_lens y \<rbrakk> \<Longrightarrow> weak_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def)

lemma comp_wb_lens: "\<lbrakk> wb_lens x; wb_lens y \<rbrakk> \<Longrightarrow> wb_lens (x ;\<^sub>L y)"
  by (unfold_locales, auto simp add: lens_comp_def wb_lens_def weak_lens.put_closure)
   
lemma comp_mwb_lens: "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> mwb_lens (x ;\<^sub>L y)"
  by (unfold_locales, auto simp add: lens_comp_def mwb_lens_def weak_lens.put_closure)

lemma source_lens_comp: "\<lbrakk> mwb_lens x; mwb_lens y \<rbrakk> \<Longrightarrow> \<S>\<^bsub>x ;\<^sub>L y\<^esub> = {s \<in> \<S>\<^bsub>y\<^esub>. get\<^bsub>y\<^esub> s \<in> \<S>\<^bsub>x\<^esub>}"
  by (auto simp add: lens_comp_def lens_source_def, blast, metis mwb_lens.put_put mwb_lens_def weak_lens.put_get)

lemma id_vwb_lens [simp]: "vwb_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma unit_vwb_lens [simp]: "vwb_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: zero_lens_def)

lemma comp_vwb_lens: "\<lbrakk> vwb_lens x; vwb_lens y \<rbrakk> \<Longrightarrow> vwb_lens (x ;\<^sub>L y)"
  by (unfold_locales, simp_all add: lens_comp_def weak_lens.put_closure)

lemma unit_ief_lens: "ief_lens 0\<^sub>L"
  by (unfold_locales, simp_all add: zero_lens_def)

text \<open>Lens plus requires that the lenses be independent to show closure.\<close>
    
lemma plus_mwb_lens:
  assumes "mwb_lens x" "mwb_lens y" "x \<bowtie> y"
  shows "mwb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales)
   apply (simp_all add: lens_plus_def prod.case_eq_if lens_indep_sym)
  apply (simp add: lens_indep_comm)
done

lemma plus_wb_lens:
  assumes "wb_lens x" "wb_lens y" "x \<bowtie> y"
  shows "wb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales, simp_all add: lens_plus_def)
  apply (simp add: lens_indep_sym prod.case_eq_if)
done

lemma plus_vwb_lens:
  assumes "vwb_lens x" "vwb_lens y" "x \<bowtie> y"
  shows "vwb_lens (x +\<^sub>L y)"
  using assms
  apply (unfold_locales, simp_all add: lens_plus_def)
   apply (simp add: lens_indep_sym prod.case_eq_if)
  apply (simp add: lens_indep_comm prod.case_eq_if)
done

lemma source_plus_lens:
  assumes "mwb_lens x" "mwb_lens y" "x \<bowtie> y"
  shows "\<S>\<^bsub>x +\<^sub>L y\<^esub> = \<S>\<^bsub>x\<^esub> \<inter> \<S>\<^bsub>y\<^esub>"
  apply (auto simp add: lens_source_def lens_plus_def)
  apply (meson assms(3) lens_indep_comm)
  apply (metis assms(1) mwb_lens.weak_get_put mwb_lens_weak weak_lens.put_closure)
done

lemma prod_mwb_lens:
  "\<lbrakk> mwb_lens X; mwb_lens Y \<rbrakk> \<Longrightarrow> mwb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: lens_prod_def prod.case_eq_if)

lemma prod_wb_lens:
  "\<lbrakk> wb_lens X; wb_lens Y \<rbrakk> \<Longrightarrow> wb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: lens_prod_def prod.case_eq_if)

lemma prod_vwb_lens:
  "\<lbrakk> vwb_lens X; vwb_lens Y \<rbrakk> \<Longrightarrow> vwb_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: lens_prod_def prod.case_eq_if)

lemma prod_bij_lens:
  "\<lbrakk> bij_lens X; bij_lens Y \<rbrakk> \<Longrightarrow> bij_lens (X \<times>\<^sub>L Y)"
  by (unfold_locales, simp_all add: lens_prod_def prod.case_eq_if)

lemma fst_vwb_lens: "vwb_lens fst\<^sub>L"
  by (unfold_locales, simp_all add: fst_lens_def prod.case_eq_if)

lemma snd_vwb_lens: "vwb_lens snd\<^sub>L"
  by (unfold_locales, simp_all add: snd_lens_def prod.case_eq_if)

lemma id_bij_lens: "bij_lens 1\<^sub>L"
  by (unfold_locales, simp_all add: id_lens_def)

lemma inv_id_lens: "inv\<^sub>L 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: lens_inv_def id_lens_def lens_create_def)

lemma lens_inv_bij: "bij_lens X \<Longrightarrow> bij_lens (inv\<^sub>L X)"
  by (unfold_locales, simp_all add: lens_inv_def lens_create_def)

lemma swap_bij_lens: "bij_lens swap\<^sub>L"
  by (unfold_locales, simp_all add: lens_plus_def prod.case_eq_if fst_lens_def snd_lens_def)

subsection \<open>Composition Laws\<close>

text \<open>Lens composition is monoidal, with unit @{term "1\<^sub>L"}, as the following theorems demonstrate. 
  It also has @{term "0\<^sub>L"} as a right annihilator. \<close>
  
lemma lens_comp_assoc: "(X ;\<^sub>L Y) ;\<^sub>L Z = X ;\<^sub>L (Y ;\<^sub>L Z)"
  by (auto simp add: lens_comp_def)

lemma lens_comp_left_id [simp]: "1\<^sub>L ;\<^sub>L X = X"
  by (simp add: id_lens_def lens_comp_def)

lemma lens_comp_right_id [simp]: "X ;\<^sub>L 1\<^sub>L = X"
  by (simp add: id_lens_def lens_comp_def)

lemma lens_comp_anhil [simp]: "wb_lens X \<Longrightarrow> 0\<^sub>L ;\<^sub>L X = 0\<^sub>L"
  by (simp add: zero_lens_def lens_comp_def comp_def)

subsection \<open>Independence Laws\<close>

text \<open>The zero lens @{term "0\<^sub>L"} is independent of any lens. This is because nothing can be observed
  or changed using @{term "0\<^sub>L"}. \<close>
  
lemma zero_lens_indep [simp]: "0\<^sub>L \<bowtie> X"
  by (auto simp add: zero_lens_def lens_indep_def)

lemma zero_lens_indep' [simp]: "X \<bowtie> 0\<^sub>L"
  by (auto simp add: zero_lens_def lens_indep_def)

text \<open>Lens independence is irreflexive, but only for effectual lenses as otherwise nothing can
  be observed.\<close>
    
lemma lens_indep_quasi_irrefl: "\<lbrakk> wb_lens x; eff_lens x \<rbrakk> \<Longrightarrow> \<not> (x \<bowtie> x)"
  by (auto simp add: lens_indep_def ief_lens_def ief_lens_axioms_def, metis (full_types) wb_lens.get_put)

text \<open>Lens independence is a congruence with respect to composition, as the following properties demonstrate.\<close>
    
lemma lens_indep_left_comp [simp]:
  "\<lbrakk> mwb_lens z; x \<bowtie> y \<rbrakk> \<Longrightarrow> (x ;\<^sub>L z) \<bowtie> (y ;\<^sub>L z)"
  apply (rule lens_indepI)
    apply (auto simp add: lens_comp_def)
   apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma lens_indep_right_comp:
  "y \<bowtie> z \<Longrightarrow> (x ;\<^sub>L y) \<bowtie> (x ;\<^sub>L z)"
  apply (auto intro!: lens_indepI simp add: lens_comp_def)
    using lens_indep_comm lens_indep_sym apply fastforce
  apply (simp add: lens_indep_sym)
done

lemma lens_indep_left_ext [intro]:
  "y \<bowtie> z \<Longrightarrow> (x ;\<^sub>L y) \<bowtie> z"
  apply (auto intro!: lens_indepI simp add: lens_comp_def)
   apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma lens_indep_right_ext [intro]:
  "x \<bowtie> z \<Longrightarrow> x \<bowtie> (y ;\<^sub>L z)"
  by (simp add: lens_indep_left_ext lens_indep_sym)

lemma lens_comp_indep_cong_left:
  "\<lbrakk> mwb_lens Z; X ;\<^sub>L Z \<bowtie> Y ;\<^sub>L Z \<rbrakk> \<Longrightarrow> X \<bowtie> Y"
  apply (rule lens_indepI)
    apply (rename_tac u v \<sigma>)
    apply (drule_tac u=u and v=v and \<sigma>="create\<^bsub>Z\<^esub> \<sigma>" in lens_indep_comm)
    apply (simp add: lens_comp_def)
    apply (meson mwb_lens_weak weak_lens.view_determination)
   apply (rename_tac v \<sigma>)
   apply (drule_tac v=v and \<sigma>="create\<^bsub>Z\<^esub> \<sigma>" in lens_indep_get)
   apply (simp add: lens_comp_def)
  apply (drule lens_indep_sym)
  apply (rename_tac u \<sigma>)
  apply (drule_tac v=u and \<sigma>="create\<^bsub>Z\<^esub> \<sigma>" in lens_indep_get)
  apply (simp add: lens_comp_def)
done

lemma lens_comp_indep_cong:
  "mwb_lens Z \<Longrightarrow> (X ;\<^sub>L Z) \<bowtie> (Y ;\<^sub>L Z) \<longleftrightarrow> X \<bowtie> Y"
  using lens_comp_indep_cong_left lens_indep_left_comp by blast

text \<open>The first and second lenses are independent since the view different parts of a product source.\<close>
    
lemma fst_snd_lens_indep [simp]:
  "fst\<^sub>L \<bowtie> snd\<^sub>L"
  by (simp add: lens_indep_def fst_lens_def snd_lens_def)

lemma snd_fst_lens_indep [simp]:
  "snd\<^sub>L \<bowtie> fst\<^sub>L"
  by (simp add: lens_indep_def fst_lens_def snd_lens_def)

lemma split_prod_lens_indep:
  assumes "mwb_lens X"
  shows "(fst\<^sub>L ;\<^sub>L X) \<bowtie> (snd\<^sub>L ;\<^sub>L X)"
  using assms fst_snd_lens_indep lens_indep_left_comp vwb_lens_mwb by blast
    
text \<open>Lens independence is preserved by summation.\<close>
    
lemma plus_pres_lens_indep [simp]: "\<lbrakk> X \<bowtie> Z; Y \<bowtie> Z \<rbrakk> \<Longrightarrow> (X +\<^sub>L Y) \<bowtie> Z"
  apply (rule lens_indepI)
    apply (simp_all add: lens_plus_def prod.case_eq_if)
   apply (simp add: lens_indep_comm)
  apply (simp add: lens_indep_sym)
done

lemma plus_pres_lens_indep' [simp]:
  "\<lbrakk> X \<bowtie> Y; X \<bowtie> Z \<rbrakk> \<Longrightarrow> X \<bowtie> Y +\<^sub>L Z"
  by (auto intro: lens_indep_sym plus_pres_lens_indep)

text \<open>Lens independence is preserved by product.\<close>
    
lemma lens_indep_prod:
  "\<lbrakk> X\<^sub>1 \<bowtie> X\<^sub>2; Y\<^sub>1 \<bowtie> Y\<^sub>2 \<rbrakk> \<Longrightarrow> X\<^sub>1 \<times>\<^sub>L Y\<^sub>1 \<bowtie> X\<^sub>2 \<times>\<^sub>L Y\<^sub>2"
  apply (rule lens_indepI)
    apply (auto simp add: lens_prod_def prod.case_eq_if lens_indep_comm map_prod_def)
   apply (simp_all add: lens_indep_sym)
done

subsection \<open>Algebraic Laws\<close>

text \<open>Lens plus distributes to the right through composition.\<close>
  
lemma plus_lens_distr: "mwb_lens Z \<Longrightarrow> (X +\<^sub>L Y) ;\<^sub>L Z = (X ;\<^sub>L Z) +\<^sub>L (Y ;\<^sub>L Z)"
  by (auto simp add: lens_comp_def lens_plus_def comp_def)

text \<open>The first lens projects the first part of a summation.\<close>
  
lemma fst_lens_plus:
  "wb_lens y \<Longrightarrow> fst\<^sub>L ;\<^sub>L (x +\<^sub>L y) = x"
  by (simp add: fst_lens_def lens_plus_def lens_comp_def comp_def)

text \<open>The second law requires independence as we have to apply x first, before y\<close>

lemma snd_lens_plus:
  "\<lbrakk> wb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> snd\<^sub>L ;\<^sub>L (x +\<^sub>L y) = y"
  apply (simp add: snd_lens_def lens_plus_def lens_comp_def comp_def)
  apply (subst lens_indep_comm)
   apply (simp_all)
done

text \<open>The swap lens switches over a summation.\<close>
  
lemma lens_plus_swap:
  "X \<bowtie> Y \<Longrightarrow> swap\<^sub>L ;\<^sub>L (X +\<^sub>L Y) = (Y +\<^sub>L X)"
  by (auto simp add: lens_plus_def fst_lens_def snd_lens_def id_lens_def lens_comp_def lens_indep_comm)

text \<open>The first, second, and swap lenses are all closely related.\<close>
    
lemma fst_snd_id_lens: "fst\<^sub>L +\<^sub>L snd\<^sub>L = 1\<^sub>L"
  by (auto simp add: lens_plus_def fst_lens_def snd_lens_def id_lens_def)

lemma swap_lens_idem: "swap\<^sub>L ;\<^sub>L swap\<^sub>L = 1\<^sub>L"
  by (simp add: fst_snd_id_lens lens_indep_sym lens_plus_swap)

lemma swap_lens_fst: "fst\<^sub>L ;\<^sub>L swap\<^sub>L = snd\<^sub>L"
  by (simp add: fst_lens_plus fst_vwb_lens)

lemma swap_lens_snd: "snd\<^sub>L ;\<^sub>L swap\<^sub>L = fst\<^sub>L"
  by (simp add: lens_indep_sym snd_lens_plus snd_vwb_lens)

text \<open>The product lens can be rewritten as a sum lens.\<close>
    
lemma prod_as_plus: "X \<times>\<^sub>L Y = X ;\<^sub>L fst\<^sub>L +\<^sub>L Y ;\<^sub>L snd\<^sub>L"
  by (auto simp add: lens_prod_def fst_lens_def snd_lens_def lens_comp_def lens_plus_def)

lemma prod_lens_id_equiv:
  "1\<^sub>L \<times>\<^sub>L 1\<^sub>L = 1\<^sub>L"
  by (auto simp add: lens_prod_def id_lens_def)

lemma prod_lens_comp_plus:
  "X\<^sub>2 \<bowtie> Y\<^sub>2 \<Longrightarrow> ((X\<^sub>1 \<times>\<^sub>L Y\<^sub>1) ;\<^sub>L (X\<^sub>2 +\<^sub>L Y\<^sub>2)) = (X\<^sub>1 ;\<^sub>L X\<^sub>2) +\<^sub>L (Y\<^sub>1 ;\<^sub>L Y\<^sub>2)"
  by (auto simp add: lens_comp_def lens_plus_def lens_prod_def prod.case_eq_if fun_eq_iff)

text \<open>The following laws about quotient are similar to their arithmetic analogues. Lens quotient 
  reverse the effect of a composition.\<close>

lemma lens_comp_quotient:
  "weak_lens Y \<Longrightarrow> (X ;\<^sub>L Y) /\<^sub>L Y = X"
  by (simp add: lens_quotient_def lens_comp_def)
    
lemma lens_quotient_id: "weak_lens X \<Longrightarrow> (X /\<^sub>L X) = 1\<^sub>L"
  by (force simp add: lens_quotient_def id_lens_def)

lemma lens_quotient_id_denom: "X /\<^sub>L 1\<^sub>L = X"
  by (simp add: lens_quotient_def id_lens_def lens_create_def)

lemma lens_quotient_unit: "weak_lens X \<Longrightarrow> (0\<^sub>L /\<^sub>L X) = 0\<^sub>L"
  by (simp add: lens_quotient_def zero_lens_def)

    
end