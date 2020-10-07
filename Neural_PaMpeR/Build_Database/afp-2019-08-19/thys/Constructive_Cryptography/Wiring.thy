section \<open>Wiring\<close>

theory Wiring imports
  Distinguisher
begin

subsection \<open>Notation\<close>
hide_const (open) Resumption.Pause Monomorphic_Monad.Pause Monomorphic_Monad.Done

no_notation Sublist.parallel (infixl "\<parallel>" 50)
no_notation plus_oracle (infix "\<oplus>\<^sub>O" 500)

notation Resource ("\<section>R\<section>")
notation Converter ("\<section>C\<section>")

alias RES = resource_of_oracle
alias CNV = converter_of_callee

alias id_intercept = "id_oracle"
notation id_oracle ("1\<^sub>I")

notation plus_oracle (infixr "\<oplus>\<^sub>O" 504)
notation parallel_oracle (infixr "\<ddagger>\<^sub>O" 504)

notation plus_intercept (infixr "\<oplus>\<^sub>I" 504)
notation parallel_intercept (infixr "\<ddagger>\<^sub>I" 504)

notation parallel_resource (infixr "\<parallel>" 501) 

notation parallel_converter (infixr "|\<^sub>\<propto>" 501)
notation parallel_converter2 (infixr "|\<^sub>=" 501)
notation comp_converter (infixr "\<odot>" 502)

notation fail_converter ("\<bottom>\<^sub>C")
notation id_converter ("1\<^sub>C")

notation "attach" (infixr "\<rhd>" 500)

subsection \<open>Wiring primitives\<close>

primrec swap_sum :: "'a + 'b \<Rightarrow> 'b + 'a" where
  "swap_sum (Inl x) = Inr x"
| "swap_sum (Inr y) = Inl y"

definition swap\<^sub>C :: "('a + 'b, 'c + 'd, 'b + 'a, 'd + 'c) converter" where
  "swap\<^sub>C = map_converter swap_sum swap_sum id id 1\<^sub>C"

definition rassocl\<^sub>C :: "('a + ('b + 'c), 'd + ('e + 'f), ('a + 'b) + 'c, ('d + 'e) + 'f) converter" where
  "rassocl\<^sub>C = map_converter lsumr rsuml id id 1\<^sub>C"
definition lassocr\<^sub>C :: "(('a + 'b) + 'c, ('d + 'e) + 'f, 'a + ('b + 'c), 'd + ('e + 'f)) converter" where
  "lassocr\<^sub>C = map_converter rsuml lsumr id id 1\<^sub>C"

definition swap_rassocl where "swap_rassocl \<equiv> lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= swap\<^sub>C) \<odot> rassocl\<^sub>C"
definition swap_lassocr where "swap_lassocr \<equiv> rassocl\<^sub>C \<odot> (swap\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> lassocr\<^sub>C"

definition parallel_wiring :: "(('a + 'b) + ('e + 'f), ('c + 'd) + ('g + 'h), ('a + 'e) + ('b + 'f), ('c + 'g) + ('d + 'h)) converter" where
  "parallel_wiring = lassocr\<^sub>C \<odot> (1\<^sub>C |\<^sub>= swap_lassocr) \<odot> rassocl\<^sub>C"

lemma WT_lassocr\<^sub>C [WT_intro]: "(\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3, \<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3) \<turnstile>\<^sub>C lassocr\<^sub>C \<surd>"
  by(coinduction)(auto simp add: lassocr\<^sub>C_def)

lemma WT_rassocl\<^sub>C [WT_intro]: "\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3), (\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3 \<turnstile>\<^sub>C rassocl\<^sub>C \<surd>"
  by(coinduction)(auto simp add: rassocl\<^sub>C_def)

lemma WT_swap\<^sub>C [WT_intro]: "\<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I>2 \<oplus>\<^sub>\<I> \<I>1 \<turnstile>\<^sub>C swap\<^sub>C \<surd>"
  by(coinduction)(auto simp add: swap\<^sub>C_def)

lemma WT_swap_lassocr [WT_intro]: "\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3), \<I>2 \<oplus>\<^sub>\<I> (\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<turnstile>\<^sub>C swap_lassocr \<surd>"
  unfolding swap_lassocr_def
  by(rule WT_converter_comp WT_lassocr\<^sub>C WT_rassocl\<^sub>C WT_converter_parallel_converter2 WT_converter_id WT_swap\<^sub>C)+

lemma WT_swap_rassocl [WT_intro]: "(\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3, (\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<oplus>\<^sub>\<I> \<I>2 \<turnstile>\<^sub>C swap_rassocl \<surd>"
  unfolding swap_rassocl_def
  by(rule WT_converter_comp WT_lassocr\<^sub>C WT_rassocl\<^sub>C WT_converter_parallel_converter2 WT_converter_id WT_swap\<^sub>C)+

lemma WT_parallel_wiring [WT_intro]:
  "(\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> (\<I>3 \<oplus>\<^sub>\<I> \<I>4), (\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>4) \<turnstile>\<^sub>C parallel_wiring \<surd>"
  unfolding parallel_wiring_def 
  by(rule WT_converter_comp WT_lassocr\<^sub>C WT_rassocl\<^sub>C WT_converter_parallel_converter2 WT_converter_id WT_swap_lassocr)+

lemma map_swap_sum_plus_oracle: includes lifting_syntax shows
  "(id ---> swap_sum ---> map_spmf (map_prod swap_sum id)) (oracle1 \<oplus>\<^sub>O oracle2) =
   (oracle2 \<oplus>\<^sub>O oracle1)"
proof ((rule ext)+; goal_cases)
  case (1 s q)
  then show ?case by (cases q) (simp_all add: spmf.map_comp o_def apfst_def prod.map_comp id_def)
qed

lemma map_\<I>_rsuml_lsumr [simp]: "map_\<I> rsuml lsumr (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) = ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3)"
proof(rule \<I>_eqI[OF Set.set_eqI], goal_cases)
  case (1 x)
  then show ?case by(cases x rule: rsuml.cases) auto
qed (auto simp add: image_image)

lemma map_\<I>_lsumr_rsuml [simp]: "map_\<I> lsumr rsuml ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) = (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3))"
proof(rule \<I>_eqI[OF Set.set_eqI], goal_cases)
  case (1 x)
  then show ?case by(cases x rule: lsumr.cases) auto
qed (auto simp add: image_image)

lemma map_\<I>_swap_sum [simp]: "map_\<I> swap_sum swap_sum (\<I>1 \<oplus>\<^sub>\<I> \<I>2) = \<I>2 \<oplus>\<^sub>\<I> \<I>1"
proof(rule \<I>_eqI[OF Set.set_eqI], goal_cases)
  case (1 x)
  then show ?case by(cases x) auto
qed (auto simp add: image_image)

definition parallel_resource1_wiring :: "('a + ('b + 'c), 'd + ('e + 'f), 'b + ('a + 'c), 'e + ('d + 'f)) converter" where
  "parallel_resource1_wiring = swap_lassocr"

lemma WT_parallel_resource1_wiring [WT_intro]: "\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3), \<I>2 \<oplus>\<^sub>\<I> (\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<turnstile>\<^sub>C parallel_resource1_wiring \<surd>"
  unfolding parallel_resource1_wiring_def by(rule WT_swap_lassocr)

lemma plossless_rassocl\<^sub>C [plossless_intro]: "plossless_converter (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) rassocl\<^sub>C"
  by coinduction (auto simp add: rassocl\<^sub>C_def)

lemma plossless_lassocr\<^sub>C [plossless_intro]: "plossless_converter ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) lassocr\<^sub>C"
  by coinduction (auto simp add: lassocr\<^sub>C_def)

lemma plossless_swap\<^sub>C [plossless_intro]: "plossless_converter (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (\<I>2 \<oplus>\<^sub>\<I> \<I>1) swap\<^sub>C"
  by coinduction (auto simp add: swap\<^sub>C_def)

lemma plossless_swap_lassocr [plossless_intro]:
  "plossless_converter (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) (\<I>2 \<oplus>\<^sub>\<I> (\<I>1 \<oplus>\<^sub>\<I> \<I>3)) swap_lassocr"
  unfolding swap_lassocr_def by(rule plossless_intro WT_intro)+

lemma rsuml_lsumr_parallel_converter2:
  "map_converter id id rsuml lsumr ((conv1 |\<^sub>= conv2) |\<^sub>= conv3) = 
   map_converter rsuml lsumr id id (conv1 |\<^sub>= conv2 |\<^sub>= conv3)"
  by(coinduction arbitrary: conv1 conv2 conv3, clarsimp split!: sum.split simp add: rel_fun_def map_gpv_conv_map_gpv'[symmetric])
    ((subst left_gpv_map[where h=id] | subst right_gpv_map[where h=id])+
      , simp add:gpv.map_comp sum.map_id0 o_def prod.map_comp id_def[symmetric]
      , subst map_gpv'_map_gpv_swap, (subst rsuml_lsumr_left_gpv_left_gpv | subst rsuml_lsumr_left_gpv_right_gpv | subst rsuml_lsumr_right_gpv)
      , auto 4 4 intro!: gpv.rel_refl_strong simp add: gpv.rel_map)+

lemma comp_lassocr\<^sub>C: "((conv1 |\<^sub>= conv2) |\<^sub>= conv3) \<odot> lassocr\<^sub>C = lassocr\<^sub>C \<odot> (conv1 |\<^sub>= conv2 |\<^sub>= conv3)"
  unfolding lassocr\<^sub>C_def
  by(subst comp_converter_map_converter2)
    (simp add: comp_converter_id_right comp_converter_map1_out comp_converter_id_left rsuml_lsumr_parallel_converter2)

lemmas comp_lassocr\<^sub>C' = comp_converter_eqs[OF comp_lassocr\<^sub>C]

lemma lsumr_rsuml_parallel_converter2:
  "map_converter id id lsumr rsuml (conv1 |\<^sub>= (conv2 |\<^sub>= conv3)) = 
   map_converter lsumr rsuml id id ((conv1 |\<^sub>= conv2) |\<^sub>= conv3)"
  by(coinduction arbitrary: conv1 conv2 conv3, clarsimp split!: sum.split simp add: rel_fun_def map_gpv_conv_map_gpv'[symmetric])
    ((subst left_gpv_map[where h=id] | subst right_gpv_map[where h=id])+
      , simp add:gpv.map_comp sum.map_id0 o_def prod.map_comp id_def[symmetric]
      , subst map_gpv'_map_gpv_swap, (subst lsumr_rsuml_left_gpv | subst lsumr_rsuml_right_gpv_left_gpv | subst lsumr_rsuml_right_gpv_right_gpv)
      , auto 4 4 intro!: gpv.rel_refl_strong simp add: gpv.rel_map)+

lemma comp_rassocl\<^sub>C:
  "(conv1 |\<^sub>= conv2 |\<^sub>= conv3) \<odot> rassocl\<^sub>C = rassocl\<^sub>C \<odot> ((conv1 |\<^sub>= conv2) |\<^sub>= conv3)"
  unfolding rassocl\<^sub>C_def
  by(subst comp_converter_map_converter2)
    (simp add: comp_converter_id_right comp_converter_map1_out comp_converter_id_left lsumr_rsuml_parallel_converter2)

lemmas comp_rassocl\<^sub>C' = comp_converter_eqs[OF comp_rassocl\<^sub>C]

lemma swap_sum_right_gpv:
  "map_gpv' id swap_sum swap_sum (right_gpv gpv) = left_gpv gpv"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split: sum.split intro: exI[where x=Fail])

lemma swap_sum_left_gpv:
  "map_gpv' id swap_sum swap_sum (left_gpv gpv) = right_gpv gpv"
  by(coinduction arbitrary: gpv)
    (auto 4 3 simp add: spmf_rel_map generat.rel_map intro!: rel_spmf_reflI rel_generat_reflI rel_funI split: sum.split intro: exI[where x=Fail])

lemma swap_sum_parallel_converter2:
  "map_converter id id swap_sum swap_sum (conv1 |\<^sub>= conv2) =
   map_converter swap_sum swap_sum id id (conv2 |\<^sub>= conv1)"
  by(coinduction arbitrary: conv1 conv2, clarsimp simp add: rel_fun_def map_gpv_conv_map_gpv'[symmetric] split!: sum.split)
    (subst map_gpv'_map_gpv_swap, (subst swap_sum_right_gpv | subst swap_sum_left_gpv), 
      auto 4 4 intro!: gpv.rel_refl_strong simp add: gpv.rel_map)+

lemma comp_swap\<^sub>C: "(conv1 |\<^sub>= conv2) \<odot> swap\<^sub>C = swap\<^sub>C \<odot> (conv2 |\<^sub>= conv1)"
  unfolding swap\<^sub>C_def
  by(subst comp_converter_map_converter2)
    (simp add: comp_converter_id_right comp_converter_map1_out comp_converter_id_left swap_sum_parallel_converter2)

lemmas comp_swap\<^sub>C' = comp_converter_eqs[OF comp_swap\<^sub>C]

lemma comp_swap_lassocr: "(conv1 |\<^sub>= conv2 |\<^sub>= conv3) \<odot> swap_lassocr = swap_lassocr \<odot> (conv2 |\<^sub>= conv1 |\<^sub>= conv3)"
  unfolding swap_lassocr_def comp_rassocl\<^sub>C' comp_converter_assoc comp_converter_parallel2' comp_swap\<^sub>C' comp_converter_id_right
  by(subst (9) comp_converter_id_left[symmetric], subst comp_converter_parallel2[symmetric])
    (simp add: comp_converter_assoc comp_lassocr\<^sub>C)

lemmas comp_swap_lassocr' = comp_converter_eqs[OF comp_swap_lassocr]

lemma comp_parallel_wiring:
  "((C1 |\<^sub>= C2) |\<^sub>= (C3 |\<^sub>= C4)) \<odot> parallel_wiring = parallel_wiring \<odot> ((C1 |\<^sub>= C3) |\<^sub>= (C2 |\<^sub>= C4))"
  unfolding parallel_wiring_def comp_lassocr\<^sub>C' comp_converter_assoc comp_converter_parallel2' comp_swap_lassocr'
  by(subst comp_converter_id_right[THEN trans, OF comp_converter_id_left[symmetric]], subst comp_converter_parallel2[symmetric])
    (simp add: comp_converter_assoc comp_rassocl\<^sub>C)

lemmas comp_parallel_wiring' = comp_converter_eqs[OF comp_parallel_wiring]

lemma attach_converter_of_resource_conv_parallel_resource:
  "converter_of_resource res |\<^sub>\<propto> 1\<^sub>C \<rhd> res' = res \<parallel> res'"
  by(coinduction arbitrary: res res')
    (auto 4 3 simp add: rel_fun_def map_lift_spmf spmf.map_comp o_def prod.map_comp spmf_rel_map bind_map_spmf map_spmf_conv_bind_spmf[symmetric] split_def split!: sum.split intro!: rel_spmf_reflI)

lemma attach_converter_of_resource_conv_parallel_resource2:
  " 1\<^sub>C |\<^sub>\<propto> converter_of_resource res \<rhd> res' = res' \<parallel> res"
  by(coinduction arbitrary: res res')
    (auto 4 3 simp add: rel_fun_def map_lift_spmf spmf.map_comp o_def prod.map_comp spmf_rel_map bind_map_spmf map_spmf_conv_bind_spmf[symmetric] split_def split!: sum.split intro!: rel_spmf_reflI)


lemma plossless_parallel_wiring [plossless_intro]:
  "plossless_converter ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> (\<I>3 \<oplus>\<^sub>\<I> \<I>4)) ((\<I>1 \<oplus>\<^sub>\<I> \<I>3) \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>4)) parallel_wiring"
  unfolding parallel_wiring_def by(rule plossless_intro WT_intro)+

lemma run_converter_lassocr [simp]:
  "run_converter lassocr\<^sub>C x = Pause (rsuml x) (\<lambda>x. Done (lsumr x, lassocr\<^sub>C))"
  by(simp add: lassocr\<^sub>C_def o_def)

lemma run_converter_rassocl [simp]:
  "run_converter rassocl\<^sub>C x = Pause (lsumr x) (\<lambda>x. Done (rsuml x, rassocl\<^sub>C))"
  by(simp add: rassocl\<^sub>C_def o_def)

lemma run_converter_swap [simp]: "run_converter swap\<^sub>C x = Pause (swap_sum x) (\<lambda>x. Done (swap_sum x, swap\<^sub>C))"
  by(simp add: swap\<^sub>C_def o_def)

definition lassocr_swap_sum where "lassocr_swap_sum = rsuml \<circ> map_sum swap_sum id \<circ> lsumr"

lemma run_converter_swap_lassocr [simp]:
  "run_converter swap_lassocr x = Pause (lassocr_swap_sum x) (
     case lsumr x of Inl _ \<Rightarrow> (\<lambda>y. case lsumr y of Inl _ \<Rightarrow> Done (lassocr_swap_sum y, swap_lassocr) | _ \<Rightarrow> Fail)
          | Inr _ \<Rightarrow> (\<lambda>y. case lsumr y of Inl _ \<Rightarrow> Fail | Inr _ \<Rightarrow> Done (lassocr_swap_sum y, swap_lassocr)))"
  by(subst sum.case_distrib[where h="\<lambda>x. inline _ x _"] |
      simp add: bind_rpv_def inline_map_gpv split_def map_gpv_conv_bind[symmetric] swap_lassocr_def o_def cong del: sum.case_cong)+
    (cases x rule: lsumr.cases, simp_all add: o_def lassocr_swap_sum_def gpv.map_comp fun_eq_iff cong: sum.case_cong split: sum.split)

definition parallel_sum_wiring where "parallel_sum_wiring = lsumr \<circ> map_sum id lassocr_swap_sum \<circ> rsuml"

(* TODO: simplify the case distinctions *)
lemma run_converter_parallel_wiring:
  "run_converter parallel_wiring x = Pause (parallel_sum_wiring x) (
    case rsuml x of Inl _ \<Rightarrow> (\<lambda>y. case rsuml y of Inl _ \<Rightarrow> Done (parallel_sum_wiring y, parallel_wiring) | _ \<Rightarrow> Fail)
                | Inr x \<Rightarrow> (case lsumr x of Inl _ \<Rightarrow> (\<lambda>y. case rsuml y of Inl _ \<Rightarrow> Fail | Inr x \<Rightarrow> (case lsumr x of Inl _ \<Rightarrow> Done (parallel_sum_wiring y, parallel_wiring) | Inr _ \<Rightarrow> Fail))
                                          | Inr _ \<Rightarrow> (\<lambda>y. case rsuml y of Inl _ \<Rightarrow> Fail | Inr x \<Rightarrow> (case lsumr x of Inl _ \<Rightarrow> Fail | Inr _ \<Rightarrow> Done (parallel_sum_wiring y, parallel_wiring)))))"
  by(simp add: parallel_wiring_def o_def cong del: sum.case_cong add: split_def map_gpv_conv_bind[symmetric])
    (subst sum.case_distrib[where h="\<lambda>x. right_rpv x _"] |
      subst sum.case_distrib[where h="\<lambda>x. inline _ x _"] |
      subst sum.case_distrib[where h=right_gpv] |
      (auto simp add: inline_map_gpv bind_rpv_def  gpv.map_comp fun_eq_iff parallel_sum_wiring_def 
        parallel_wiring_def[symmetric] sum.case_distrib o_def intro: sym cong del: sum.case_cong split!: sum.split))+

lemma bound_lassocr\<^sub>C [interaction_bound]: "interaction_any_bounded_converter lassocr\<^sub>C 1"
  unfolding lassocr\<^sub>C_def by interaction_bound_converter simp

lemma bound_rassocl\<^sub>C [interaction_bound]: "interaction_any_bounded_converter rassocl\<^sub>C 1"
  unfolding rassocl\<^sub>C_def by interaction_bound_converter simp

lemma bound_swap\<^sub>C [interaction_bound]: "interaction_any_bounded_converter swap\<^sub>C 1"
  unfolding swap\<^sub>C_def by interaction_bound_converter simp

lemma bound_swap_rassocl [interaction_bound]: "interaction_any_bounded_converter swap_rassocl 1"
  unfolding swap_rassocl_def by interaction_bound_converter simp

lemma bound_swap_lassocr [interaction_bound]: "interaction_any_bounded_converter swap_lassocr 1"
  unfolding swap_lassocr_def by interaction_bound_converter simp

lemma bound_parallel_wiring [interaction_bound]: "interaction_any_bounded_converter parallel_wiring 1"
  unfolding parallel_wiring_def by interaction_bound_converter simp

subsection \<open>Characterization of wirings\<close>

type_synonym ('a, 'b, 'c, 'd) wiring = "('a \<Rightarrow> 'c) \<times> ('d \<Rightarrow> 'b)"

inductive wiring :: "('a, 'b) \<I> \<Rightarrow> ('c, 'd) \<I> \<Rightarrow> ('a, 'b, 'c, 'd) converter \<Rightarrow> ('a, 'b, 'c, 'd) wiring \<Rightarrow> bool"
  for \<I> \<I>' cnv
  where
    wiring:
    "wiring \<I> \<I>' cnv (f, g)" if
    "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<sim> map_converter id id f g 1\<^sub>C"
    "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<surd>"

lemmas wiringI = wiring
hide_fact wiring

lemma wiringD:
  assumes "wiring \<I> \<I>' cnv (f, g)"
  shows wiringD_eq: "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<sim> map_converter id id f g 1\<^sub>C"
    and wiringD_WT: "\<I>,\<I>' \<turnstile>\<^sub>C cnv \<surd>"
  using assms by(cases, blast)+

named_theorems wiring_intro "introduction rules for wiring"

definition apply_wiring :: "('a, 'b, 'c, 'd) wiring \<Rightarrow> ('s, 'c, 'd) oracle' \<Rightarrow> ('s, 'a, 'b) oracle'"
  where "apply_wiring = (\<lambda>(f, g). map_fun id (map_fun f (map_spmf (map_prod g id))))"

lemma apply_wiring_simps: "apply_wiring (f, g) = map_fun id (map_fun f (map_spmf (map_prod g id)))"
  by(simp add: apply_wiring_def)

lemma attach_wiring_resource_of_oracle:
  assumes wiring: "wiring \<I>1 \<I>2 conv fg"
    and WT: "\<I>2 \<turnstile>res RES res s \<surd>"
    and outs: "outs_\<I> \<I>1 = UNIV"
  shows "conv \<rhd> RES res s = RES (apply_wiring fg res) s"
  using wiring
proof cases
  case (wiring f g)
  have "\<I>_full,\<I>2 \<turnstile>\<^sub>C conv \<sim> map_converter id id f g 1\<^sub>C" using wiring(2)
    by(rule eq_\<I>_converter_mono)(simp_all add: le_\<I>_def outs)
  with WT have "conv \<rhd> RES res s = map_converter id id f g 1\<^sub>C \<rhd> RES res s"
    by(rule eq_\<I>_attach)
  also have "\<dots> = RES (apply_wiring fg res) s"
    by(simp add: attach_map_converter map_resource_resource_of_oracle prod.map_id0 option.map_id0 map_fun_id apply_wiring_def wiring(1))
  finally show ?thesis .
qed

lemma wiring_id_converter [simp, wiring_intro]: "wiring \<I> \<I> 1\<^sub>C (id, id)"
  using wiring.intros[of \<I> \<I> "1\<^sub>C" id id]
  by(simp add: eq_\<I>_converter_reflI)

lemma apply_wiring_id [simp]: "apply_wiring (id, id) res = res"
  by(simp add: apply_wiring_simps prod.map_id0 option.map_id0 map_fun_id)

definition attach_wiring :: "('a, 'b, 'c, 'd) wiring \<Rightarrow> ('s \<Rightarrow> 'c \<Rightarrow> ('d \<times> 's, 'e, 'f) gpv) \<Rightarrow> ('s \<Rightarrow> 'a \<Rightarrow> ('b \<times> 's, 'e, 'f) gpv)"
  where "attach_wiring = (\<lambda>(f, g). map_fun id (map_fun f (map_gpv (map_prod g id) id)))"

lemma attach_wiring_simps: "attach_wiring (f, g) = map_fun id (map_fun f (map_gpv (map_prod g id) id))"
  by(simp add: attach_wiring_def)

lemma comp_wiring_converter_of_callee:
  assumes wiring: "wiring \<I>1 \<I>2 conv w"
    and WT: "\<I>2, \<I>3 \<turnstile>\<^sub>C CNV callee s \<surd>"
  shows "\<I>1, \<I>3 \<turnstile>\<^sub>C conv \<odot> CNV callee s \<sim> CNV (attach_wiring w callee) s"
  using wiring
proof cases
  case (wiring f g)
  from wiring(2) have "\<I>1,\<I>3 \<turnstile>\<^sub>C conv \<odot> CNV callee s \<sim> map_converter id id f g 1\<^sub>C \<odot> CNV callee s"
    by(rule eq_\<I>_comp_cong)(rule eq_\<I>_converter_reflI[OF WT])
  also have "map_converter id id f g 1\<^sub>C \<odot> CNV callee s = map_converter f g id id (CNV callee s)"
    by(subst comp_converter_map_converter1)(simp add: comp_converter_id_left)
  also have "\<dots> = CNV (attach_wiring w callee) s"
    by(simp add: map_converter_of_callee attach_wiring_simps wiring(1) map_gpv_conv_map_gpv')
  finally show ?thesis .
qed

definition comp_wiring :: "('a, 'b, 'c, 'd) wiring \<Rightarrow> ('c, 'd, 'e, 'f) wiring \<Rightarrow> ('a, 'b, 'e, 'f) wiring" (infixl "\<circ>\<^sub>w" 55)
  where "comp_wiring = (\<lambda>(f, g) (f', g'). (f' \<circ> f, g \<circ> g'))"

lemma comp_wiring_simps: "comp_wiring (f, g) (f', g') = (f' \<circ> f, g \<circ> g')"
  by(simp add: comp_wiring_def)

lemma wiring_comp_converterI [wiring_intro]:
  "wiring \<I> \<I>'' (conv1 \<odot> conv2) (fg \<circ>\<^sub>w fg')" if "wiring \<I> \<I>' conv1 fg" "wiring \<I>' \<I>'' conv2 fg'"
proof -
  from that(1) obtain f g
    where conv1: "\<I>,\<I>' \<turnstile>\<^sub>C conv1 \<sim> map_converter id id f g 1\<^sub>C"
      and WT1: "\<I>, \<I>' \<turnstile>\<^sub>C conv1 \<surd>"
      and [simp]: "fg = (f, g)"
    by cases
  from that(2) obtain f' g' 
    where conv2: "\<I>',\<I>'' \<turnstile>\<^sub>C conv2 \<sim> map_converter id id f' g' 1\<^sub>C"
      and WT2: "\<I>', \<I>'' \<turnstile>\<^sub>C conv2 \<surd>"
      and [simp]: "fg' = (f', g')"
    by cases
  have *: "(fg \<circ>\<^sub>w fg') = (f' \<circ> f, g \<circ> g')" by(simp add: comp_wiring_simps)
  have "\<I>,\<I>'' \<turnstile>\<^sub>C conv1 \<odot> conv2 \<sim> map_converter id id f g 1\<^sub>C \<odot> map_converter id id f' g' 1\<^sub>C"
    using conv1 conv2 by(rule eq_\<I>_comp_cong)
  also have "map_converter id id f g 1\<^sub>C \<odot> map_converter id id f' g' 1\<^sub>C = map_converter id id (f' \<circ> f) (g \<circ> g') 1\<^sub>C"
    by(simp add: comp_converter_map_converter2 comp_converter_id_right)
  also have "\<I>,\<I>'' \<turnstile>\<^sub>C conv1 \<odot> conv2 \<surd>" using WT1 WT2 by(rule WT_converter_comp)
  ultimately show ?thesis unfolding * ..
qed

definition parallel2_wiring
  :: "('a, 'b, 'c, 'd) wiring \<Rightarrow> ('a', 'b', 'c', 'd') wiring
   \<Rightarrow> ('a + 'a', 'b + 'b', 'c + 'c', 'd + 'd') wiring" (infix "|\<^sub>w" 501) where
  "parallel2_wiring = (\<lambda>(f, g) (f', g'). (map_sum f f', map_sum g g'))"

lemma parallel2_wiring_simps:
  "parallel2_wiring (f, g) (f', g') = (map_sum f f', map_sum g g')"
  by(simp add: parallel2_wiring_def)

lemma wiring_parallel_converter2 [simp, wiring_intro]:
  assumes "wiring \<I>1 \<I>1' conv1 fg"
    and "wiring \<I>2 \<I>2' conv2 fg'"
  shows "wiring (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (\<I>1' \<oplus>\<^sub>\<I> \<I>2') (conv1 |\<^sub>= conv2) (fg |\<^sub>w fg')"
proof -
  from assms(1) obtain f1 g1
    where conv1: "\<I>1,\<I>1' \<turnstile>\<^sub>C conv1 \<sim> map_converter id id f1 g1 1\<^sub>C"
      and WT1: "\<I>1, \<I>1' \<turnstile>\<^sub>C conv1 \<surd>"
      and [simp]: "fg = (f1, g1)"
    by cases
  from assms(2) obtain f2 g2 
    where conv2: "\<I>2,\<I>2' \<turnstile>\<^sub>C conv2 \<sim> map_converter id id f2 g2 1\<^sub>C"
      and WT2: "\<I>2, \<I>2' \<turnstile>\<^sub>C conv2 \<surd>"
      and [simp]: "fg' = (f2, g2)"
    by cases
  from eq_\<I>_converterD_WT1[OF conv1 WT1] have \<I>1: "\<I>1 \<le> map_\<I> f1 g1 \<I>1'" by(rule WT_map_converter_idD)
  from eq_\<I>_converterD_WT1[OF conv2 WT2] have \<I>2: "\<I>2 \<le> map_\<I> f2 g2 \<I>2'" by(rule WT_map_converter_idD)
  have WT': "\<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I>1' \<oplus>\<^sub>\<I> \<I>2' \<turnstile>\<^sub>C map_converter id id (map_sum f1 f2) (map_sum g1 g2) 1\<^sub>C \<surd>"
    by(auto intro!: WT_converter_map_converter WT_converter_mono[OF WT_converter_id order_refl] \<I>1 \<I>2)
  have "\<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I>1' \<oplus>\<^sub>\<I> \<I>2' \<turnstile>\<^sub>C conv1 |\<^sub>= conv2 \<sim> map_converter id id f1 g1 1\<^sub>C |\<^sub>= map_converter id id f2 g2 1\<^sub>C"
    using conv1 conv2 by(rule parallel_converter2_eq_\<I>_cong)
  also have "map_converter id id f1 g1 1\<^sub>C |\<^sub>= map_converter id id f2 g2 1\<^sub>C = (1\<^sub>C |\<^sub>= 1\<^sub>C) \<odot> map_converter id id (map_sum f1 f2) (map_sum g1 g2) 1\<^sub>C"
    by(simp add: parallel_converter2_map2_out parallel_converter2_map1_out map_sum.comp sum.map_id0 comp_converter_map_converter2[of _ id id, simplified] comp_converter_id_right)
  also have "\<I>1 \<oplus>\<^sub>\<I> \<I>2, \<I>1' \<oplus>\<^sub>\<I> \<I>2' \<turnstile>\<^sub>C \<dots> \<sim> 1\<^sub>C \<odot> map_converter id id (map_sum f1 f2) (map_sum g1 g2) 1\<^sub>C"
    by(rule eq_\<I>_comp_cong[OF parallel_converter2_id_id])(rule eq_\<I>_converter_reflI[OF WT'])
  finally show ?thesis using WT1 WT2
    by(auto simp add: parallel2_wiring_simps comp_converter_id_left intro!: wiringI WT_converter_parallel_converter2)
qed

lemma apply_parallel2 [simp]:
  "apply_wiring (fg |\<^sub>w fg') (res1 \<oplus>\<^sub>O res2) = (apply_wiring fg res1 \<oplus>\<^sub>O apply_wiring fg' res2)"
proof -
  have[simp]: "fg = (f1, g1) \<Longrightarrow> fg' = (f2, g2) \<Longrightarrow>
       map_spmf (map_prod (map_sum g1 g2) id) ((res1 \<oplus>\<^sub>O res2) s (map_sum f1 f2 q)) =
       ((\<lambda>s q. map_spmf (map_prod g1 id) (res1 s (f1 q))) \<oplus>\<^sub>O (\<lambda>s q. map_spmf (map_prod g2 id) (res2 s (f2 q)))) s q" for f1 g1 f2 g2 s q
    by(cases q)(simp_all add: spmf.map_comp o_def apfst_def prod.map_comp split!:sum.splits)

  show ?thesis 
    by(cases fg; cases fg') (clarsimp simp add: parallel2_wiring_simps apply_wiring_simps fun_eq_iff map_fun_def o_def)
qed

lemma apply_comp_wiring [simp]: "apply_wiring (fg \<circ>\<^sub>w fg') res = apply_wiring fg (apply_wiring fg' res)"
  by(cases fg; cases fg')(simp add: comp_wiring_simps apply_wiring_simps map_fun_def fun_eq_iff spmf.map_comp prod.map_comp o_def id_def)

definition lassocr\<^sub>w :: "(('a + 'b) + 'c, ('d + 'e) + 'f, 'a + ('b + 'c), 'd + ('e + 'f)) wiring" 
  where "lassocr\<^sub>w = (rsuml, lsumr)"

definition rassocl\<^sub>w :: "('a + ('b + 'c), 'd + ('e + 'f), ('a + 'b) + 'c, ('d + 'e) + 'f) wiring" 
  where "rassocl\<^sub>w = (lsumr, rsuml)"

definition swap\<^sub>w :: "('a + 'b, 'c + 'd, 'b + 'a, 'd + 'c) wiring" where 
  "swap\<^sub>w = (swap_sum, swap_sum)"

lemma wiring_lassocr [simp, wiring_intro]:
  "wiring ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) lassocr\<^sub>C lassocr\<^sub>w"
  unfolding lassocr\<^sub>C_def lassocr\<^sub>w_def
  by(subst map_converter_id_move_right)(auto intro!: wiringI eq_\<I>_converter_reflI WT_converter_map_converter)

lemma wiring_rassocl [simp, wiring_intro]:
  "wiring (\<I>1 \<oplus>\<^sub>\<I> (\<I>2 \<oplus>\<^sub>\<I> \<I>3)) ((\<I>1 \<oplus>\<^sub>\<I> \<I>2) \<oplus>\<^sub>\<I> \<I>3) rassocl\<^sub>C rassocl\<^sub>w"
  unfolding rassocl\<^sub>C_def rassocl\<^sub>w_def
  by(subst map_converter_id_move_right)(auto intro!: wiringI eq_\<I>_converter_reflI WT_converter_map_converter)

lemma wiring_swap [simp, wiring_intro]: "wiring (\<I>1 \<oplus>\<^sub>\<I> \<I>2) (\<I>2 \<oplus>\<^sub>\<I> \<I>1) swap\<^sub>C swap\<^sub>w"
  unfolding swap\<^sub>C_def swap\<^sub>w_def
  by(subst map_converter_id_move_right)(auto intro!: wiringI eq_\<I>_converter_reflI WT_converter_map_converter)

lemma apply_lassocr\<^sub>w [simp]: "apply_wiring lassocr\<^sub>w (res1 \<oplus>\<^sub>O res2 \<oplus>\<^sub>O res3) = (res1 \<oplus>\<^sub>O res2) \<oplus>\<^sub>O res3"
  by(simp add: apply_wiring_def lassocr\<^sub>w_def map_rsuml_plus_oracle)

lemma apply_rassocl\<^sub>w [simp]: "apply_wiring rassocl\<^sub>w ((res1 \<oplus>\<^sub>O res2) \<oplus>\<^sub>O res3) = res1 \<oplus>\<^sub>O res2 \<oplus>\<^sub>O res3"
  by(simp add: apply_wiring_def rassocl\<^sub>w_def map_lsumr_plus_oracle)

lemma apply_swap\<^sub>w [simp]: "apply_wiring swap\<^sub>w (res1 \<oplus>\<^sub>O res2) = res2 \<oplus>\<^sub>O res1"
  by(simp add: apply_wiring_def swap\<^sub>w_def map_swap_sum_plus_oracle)

end