(*
 * Title:      Decreasing Diagrams II  
 * Author:     Bertram Felgenhauer (2015)
 * Maintainer: Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at>
 * License:    LGPL
 *)
section \<open>Decreasing Diagrams\<close>

theory Decreasing_Diagrams_II
imports
  Decreasing_Diagrams_II_Aux
  "HOL-Cardinals.Wellorder_Extension"
  "Abstract-Rewriting.Abstract_Rewriting"
begin

subsection \<open>Greek accents\<close>

datatype accent = Acute | Grave | Macron

lemma UNIV_accent: "UNIV = { Acute, Grave, Macron }"
using accent.nchotomy by blast

lemma finite_accent: "finite (UNIV :: accent set)"
by (simp add: UNIV_accent)

type_synonym 'a letter = "accent \<times> 'a"

definition letter_less :: "('a \<times> 'a) set \<Rightarrow> ('a letter \<times> 'a letter) set" where
  [simp]: "letter_less R = {(a,b). (snd a, snd b) \<in> R}"

lemma mono_letter_less: "mono letter_less"
by (auto simp add: mono_def)


subsection \<open>Comparing Greek strings\<close>

type_synonym 'a greek = "'a letter list"

definition adj_msog :: "'a greek \<Rightarrow> 'a greek \<Rightarrow> ('a letter \<times> 'a greek) \<Rightarrow> ('a letter \<times> 'a greek)"
where
  "adj_msog xs zs l \<equiv>
    case l of (y,ys) \<Rightarrow> (y, case fst y of Acute \<Rightarrow> ys @ zs | Grave \<Rightarrow> xs @ ys | Macron \<Rightarrow> ys)"

definition ms_of_greek :: "'a greek \<Rightarrow> ('a letter \<times> 'a greek) multiset" where
  "ms_of_greek as = mset
    (map (\<lambda>(xs, y, zs) \<Rightarrow> adj_msog xs zs (y, [])) (list_splits as))"

lemma adj_msog_adj_msog[simp]:
  "adj_msog xs zs (adj_msog xs' zs' y) = adj_msog (xs @ xs') (zs' @ zs) y"
by (auto simp: adj_msog_def split: accent.splits prod.splits)

lemma compose_adj_msog[simp]: "adj_msog xs zs \<circ> adj_msog xs' zs' = adj_msog (xs @ xs') (zs' @ zs)"
by (simp add: comp_def)

lemma adj_msog_single:
  "adj_msog xs zs (x,[]) = (x, (case fst x of Grave \<Rightarrow> xs | Acute \<Rightarrow> zs | Macron \<Rightarrow> []))"
by (simp add: adj_msog_def split: accent.splits)

lemma ms_of_greek_elem:
  assumes "(x,xs) \<in> set_mset (ms_of_greek ys)"
  shows "x \<in> set ys"
using assms by (auto dest: elem_list_splits_elem simp: adj_msog_def ms_of_greek_def)

lemma ms_of_greek_shorter:
  assumes "(x, t) \<in># ms_of_greek s"
  shows "length s > length t"
using assms[unfolded ms_of_greek_def in_multiset_in_set]
by (auto simp: elem_list_splits_length adj_msog_def split: accent.splits)

lemma msog_append: "ms_of_greek (xs @ ys) = image_mset (adj_msog [] ys) (ms_of_greek xs) +
  image_mset (adj_msog xs []) (ms_of_greek ys)"
by (auto simp: ms_of_greek_def list_splits_append multiset.map_comp comp_def prod.case_distrib)

definition nest :: "('a \<times> 'a) set \<Rightarrow> ('a greek \<times> 'a greek) set \<Rightarrow> ('a greek \<times> 'a greek) set" where
  [simp]: "nest r s = {(a,b). (ms_of_greek a, ms_of_greek b) \<in> mult (letter_less r <*lex*> s)}"

lemma mono_nest: "mono (nest r)"
unfolding mono_def
proof (intro allI impI subsetI)
  fix R S x
  assume 1: "R \<subseteq> S" and 2: "x \<in> nest r R"
  from 1 have "mult (letter_less r <*lex*> R) \<subseteq> mult (letter_less r <*lex*> S)"
  using mono_mult mono_lex2[of "letter_less r"] unfolding mono_def by blast
  with 2 show "x \<in> nest r S" by auto
qed

lemma nest_mono[mono_set]: "x \<subseteq> y \<Longrightarrow> (a,b) \<in> nest r x \<longrightarrow> (a,b) \<in> nest r y"
using mono_nest[unfolded mono_def, rule_format, of x y r] by blast

definition greek_less :: "('a \<times> 'a) set \<Rightarrow> ('a greek \<times> 'a greek) set" where
  "greek_less r = lfp (nest r)"

lemma greek_less_unfold:
  "greek_less r = nest r (greek_less r)"
using mono_nest[of r] lfp_unfold[of "nest r"] by (simp add: greek_less_def)


subsection \<open>Preservation of strict partial orders\<close>

lemma strict_order_letter_less:
  assumes "strict_order r"
  shows "strict_order (letter_less r)"
using assms unfolding irrefl_def trans_def letter_less_def by fast

lemma strict_order_nest:
  assumes r: "strict_order r" and R: "strict_order R"
  shows "strict_order (nest r R)"
proof -
  have "strict_order (mult (letter_less r <*lex*> R))"
  using strict_order_letter_less[of r] irrefl_lex_prod[of "letter_less r" R]
    trans_lex_prod[of "letter_less r" R] strict_order_mult[of "letter_less r <*lex*> R"] assms
  by fast
  from this show "strict_order (nest r R)" unfolding nest_def trans_def irrefl_def by fast
qed

lemma strict_order_greek_less:
  assumes "strict_order r"
  shows "strict_order (greek_less r)"
by (simp add: greek_less_def strict_order_lfp[OF mono_nest strict_order_nest[OF assms]])

lemma trans_letter_less:
  assumes "trans r"
  shows "trans (letter_less r)"
using assms unfolding trans_def letter_less_def by fast

lemma trans_order_nest: "trans (nest r R)"
using trans_mult unfolding nest_def trans_def by fast

lemma trans_greek_less[simp]: "trans (greek_less r)"
by (subst greek_less_unfold) (rule trans_order_nest)

lemma mono_greek_less: "mono greek_less"
unfolding greek_less_def mono_def
proof (intro allI impI lfp_mono)
  fix r s :: "('a \<times> 'a) set" and R :: "('a greek \<times> 'a greek) set"
  assume "r \<subseteq> s"
  then have "letter_less r <*lex*> R \<subseteq> letter_less s <*lex*> R"
  using mono_letter_less mono_lex1 unfolding mono_def by metis
  then show "nest r R \<subseteq> nest s R" using mono_mult unfolding nest_def mono_def by blast
qed


subsection \<open>Involution\<close>

definition inv_letter :: "'a letter \<Rightarrow> 'a letter" where
  "inv_letter l \<equiv>
    case l of (a, x) \<Rightarrow> (case a of Grave \<Rightarrow> Acute | Acute \<Rightarrow> Grave | Macron \<Rightarrow> Macron, x)"

lemma inv_letter_pair[simp]:
  "inv_letter (a, x) = (case a of Grave \<Rightarrow> Acute | Acute \<Rightarrow> Grave | Macron \<Rightarrow> Macron, x)"
by (simp add: inv_letter_def)

lemma snd_inv_letter[simp]:
  "snd (inv_letter x) = snd x"
by (simp add: inv_letter_def split: prod.splits)

lemma inv_letter_invol[simp]:
  "inv_letter (inv_letter x) = x"
by (simp add: inv_letter_def split: prod.splits accent.splits)

lemma inv_letter_mono[simp]:
  assumes "(x, y) \<in> letter_less r"
  shows "(inv_letter x, inv_letter y) \<in> letter_less r"
using assms by simp

definition inv_greek :: "'a greek \<Rightarrow> 'a greek" where
  "inv_greek s = rev (map inv_letter s)"

lemma inv_greek_invol[simp]:
  "inv_greek (inv_greek s) = s"
by (simp add: inv_greek_def rev_map comp_def)

lemma inv_greek_append:
  "inv_greek (s @ t) = inv_greek t @ inv_greek s"
by (simp add: inv_greek_def)

definition inv_msog :: "('a letter \<times> 'a greek) multiset \<Rightarrow> ('a letter \<times> 'a greek) multiset" where
  "inv_msog M = image_mset (\<lambda>(x, t). (inv_letter x, inv_greek t)) M"

lemma inv_msog_invol[simp]:
  "inv_msog (inv_msog M) = M"
by (simp add: inv_msog_def multiset.map_comp comp_def prod.case_distrib)

lemma ms_of_greek_inv_greek:
  "ms_of_greek (inv_greek M) = inv_msog (ms_of_greek M)"
unfolding inv_msog_def inv_greek_def ms_of_greek_def list_splits_rev list_splits_map mset_map
  multiset.map_comp mset_rev inv_letter_def adj_msog_def
by (rule cong[OF cong[OF refl[of "image_mset"]] refl]) (auto split: accent.splits)

lemma inv_greek_mono:
  assumes "trans r" and "(s, t) \<in> greek_less r"
  shows "(inv_greek s, inv_greek t) \<in> greek_less r"
using assms(2)
proof (induct "length s + length t" arbitrary: s t rule: less_induct)
  note * = trans_lex_prod[OF trans_letter_less[OF \<open>trans r\<close>] trans_greek_less[of r]]
  case (less s t)
  have "(inv_msog (ms_of_greek s), inv_msog (ms_of_greek t)) \<in> mult (letter_less r <*lex*> greek_less r)"
  unfolding inv_msog_def
  proof (induct rule: mult_of_image_mset[OF * *])
    case (1 x y) thus ?case
    by (auto intro: less(1) split: prod.splits dest!: ms_of_greek_shorter)
  next
    case 2 thus ?case using less(2) by (subst(asm) greek_less_unfold) simp
  qed
  thus ?case by (subst greek_less_unfold) (auto simp: ms_of_greek_inv_greek)
qed


subsection \<open>Monotonicity of @{term "greek_less r"}\<close>

lemma greek_less_rempty[simp]:
  "(a,[]) \<in> greek_less r \<longleftrightarrow> False"
by (subst greek_less_unfold) (auto simp: ms_of_greek_def)

lemma greek_less_nonempty:
  assumes "b \<noteq> []"
  shows "(a,b) \<in> greek_less r \<longleftrightarrow> (a,b) \<in> nest r (greek_less r)"
by (subst greek_less_unfold) simp

lemma greek_less_lempty[simp]:
  "([],b) \<in> greek_less r \<longleftrightarrow> b \<noteq> []"
proof
  assume "([],b) \<in> greek_less r"
  then show "b \<noteq> []" using greek_less_rempty by fast
next
  assume "b \<noteq> []"
  then show "([],b) \<in> greek_less r"
  unfolding greek_less_nonempty[OF \<open>b \<noteq> []\<close>] by (simp add: ms_of_greek_def)
qed

lemma greek_less_singleton:
  "(a, b) \<in> letter_less r \<Longrightarrow> ([a], [b]) \<in> greek_less r"
by (subst greek_less_unfold) (auto split: accent.splits simp: adj_msog_def ms_of_greek_def)

lemma ms_of_greek_cons:
  "ms_of_greek (x # s) = {# adj_msog [] s (x,[]) #} + image_mset (adj_msog [x] []) (ms_of_greek s)"
using msog_append[of "[x]" s]
by (auto simp add: adj_msog_def ms_of_greek_def accent.splits)

lemma greek_less_cons_mono:
  assumes "trans r"
  shows "(s, t) \<in> greek_less r \<Longrightarrow> (x # s, x # t) \<in> greek_less r"
proof (induct "length s + length t" arbitrary: s t rule: less_induct)
  note * = trans_lex_prod[OF trans_letter_less[OF \<open>trans r\<close>] trans_greek_less[of r]]
  case (less s t)
  {
    fix M have "(M + image_mset (adj_msog [x] []) (ms_of_greek s),
      M + image_mset (adj_msog [x] []) (ms_of_greek t)) \<in> mult (letter_less r <*lex*> greek_less r)"
    proof (rule mult_on_union, induct rule: mult_of_image_mset[OF * *])
      case (1 x y) thus ?case unfolding adj_msog_def
      by (auto intro: less(1) split: prod.splits accent.splits dest!: ms_of_greek_shorter)
    next
      case 2 thus ?case using less(2) by (subst(asm) greek_less_unfold) simp
    qed
  }
  moreover {
    fix N have "({# adj_msog [] s (x,[]) #} + N,{# adj_msog [] t (x,[]) #} + N) \<in>
      (mult (letter_less r <*lex*> greek_less r))\<^sup>="
    by (auto simp: adj_msog_def less split: accent.splits) }
  ultimately show ?case using transD[OF trans_mult]
  by (subst greek_less_unfold) (fastforce simp: ms_of_greek_cons)
qed

lemma greek_less_app_mono2:
  assumes "trans r" and "(s, t) \<in> greek_less r"
  shows "(p @ s, p @ t) \<in> greek_less r"
using assms by (induct p) (auto simp add: greek_less_cons_mono)

lemma greek_less_app_mono1:
  assumes "trans r" and "(s, t) \<in> greek_less r"
  shows "(s @ p, t @ p) \<in> greek_less r"
using inv_greek_mono[of r "inv_greek p @ inv_greek s" "inv_greek p @ inv_greek t"]
by (simp add: assms inv_greek_append inv_greek_mono greek_less_app_mono2)


subsection \<open>Well-founded-ness of @{term "greek_less r"}\<close>

lemma greek_embed:
  assumes "trans r"
  shows "list_emb (\<lambda>a b. (a, b): reflcl (letter_less r)) a b \<Longrightarrow> (a, b) \<in> reflcl (greek_less r)"
proof (induct rule: list_emb.induct)
  case (list_emb_Cons a b y) thus ?case
  using trans_greek_less[unfolded trans_def] \<open>trans r\<close>
    greek_less_app_mono1[of r "[]" "[y]" a] greek_less_app_mono2[of r a b "[y]"] by auto
next
  case (list_emb_Cons2 x y a b) thus ?case
  using trans_greek_less[unfolded trans_def] \<open>trans r\<close> greek_less_singleton[of x y r]
    greek_less_app_mono1[of r "[x]" "[y]" a] greek_less_app_mono2[of r a b "[y]"] by auto
qed simp

lemma wqo_letter_less:
  assumes t: "trans r" and w: "wqo_on (\<lambda>a b. (a, b) \<in> r\<^sup>=) UNIV"
  shows "wqo_on (\<lambda>a b. (a, b) \<in> (letter_less r)\<^sup>=) UNIV"
proof (rule wqo_on_hom[of _ id _ "prod_le (=) (\<lambda>a b. (a, b) \<in> r\<^sup>=)", unfolded image_id id_apply])
  show "wqo_on (prod_le ((=) :: accent \<Rightarrow> accent \<Rightarrow> bool) (\<lambda>a b. (a, b) \<in> r\<^sup>=)) UNIV"
  by (rule dickson[OF finite_eq_wqo_on[OF finite_accent] w, unfolded UNIV_Times_UNIV])
qed (insert t, auto simp: transp_on_def trans_def prod_le_def)

lemma wf_greek_less:
  assumes "wf r" and "trans r"
  shows "wf (greek_less r)"
proof -
  obtain q where "r \<subseteq> q" and "well_order q" by (metis total_well_order_extension \<open>wf r\<close>)
  define q' where "q' = q - Id"
  from \<open>well_order q\<close> have "reflcl q' = q"
  by (auto simp add: well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def
      refl_on_def q'_def)
  from \<open>well_order q\<close> have "trans q'" and "irrefl q'"
  unfolding well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def antisym_def
    trans_def irrefl_def q'_def by blast+
  from \<open>r \<subseteq> q\<close> \<open>wf r\<close> have "r \<subseteq> q'" by (auto simp add: q'_def)
  have "wqo_on (\<lambda>a b. (a,b) \<in> (greek_less q')\<^sup>=) UNIV"
  proof (intro wqo_on_hom[of "(\<lambda>a b. (a, b) \<in> (greek_less q')\<^sup>=)" "id" UNIV
         "list_emb (\<lambda>a b. (a, b) \<in> (letter_less q')\<^sup>=)", unfolded surj_id])
    show "transp_on (\<lambda>a b. (a, b) \<in> (greek_less q')\<^sup>=) UNIV"
    using trans_greek_less[of q'] unfolding trans_def transp_on_def by blast
  next
    show "\<forall>x\<in>UNIV. \<forall>y\<in>UNIV. list_emb (\<lambda>a b. (a, b) \<in> (letter_less q')\<^sup>=) x y \<longrightarrow>
          (id x, id y) \<in> (greek_less q')\<^sup>="
    using greek_embed[OF \<open>trans q'\<close>] by auto
  next
    show "wqo_on (list_emb (\<lambda>a b. (a, b) \<in> (letter_less q')\<^sup>=)) UNIV"
    using higman[OF wqo_letter_less[OF \<open>trans q'\<close>]] \<open>well_order q\<close> \<open>reflcl q' = q\<close>
    by (auto simp: well_order_implies_wqo)
  qed
  with wqo_on_imp_wfp_on[OF this] strict_order_strict[OF strict_order_greek_less]
    \<open>irrefl q'\<close> \<open>trans q'\<close>
  have "wfp_on (\<lambda>a b. (a, b) \<in> greek_less q') UNIV" by force
  then show ?thesis
  using mono_greek_less \<open>r \<subseteq> q'\<close> wf_subset unfolding wf_iff_wfp_on[symmetric] mono_def by metis
qed


subsection \<open>Basic Comparisons\<close>

lemma pairwise_imp_mult:
  assumes "N \<noteq> {#}" and "\<forall>x \<in> set_mset M. \<exists>y \<in> set_mset N. (x, y) \<in> r"
  shows "(M, N) \<in> mult r"
using assms one_step_implies_mult[of _ _ _ "{#}"] by auto

lemma singleton_greek_less:
  assumes as: "snd ` set as \<subseteq> under r b"
  shows "(as, [(a,b)]) \<in> greek_less r"
proof -
  {
    fix e assume "e \<in> set_mset (ms_of_greek as)"
    with as ms_of_greek_elem[of _ _ as]
    have "(e, ((a,b),[])) \<in> letter_less r <*lex*> greek_less r"
    by (cases e) (fastforce simp: adj_msog_def under_def)
  }
  moreover have "ms_of_greek [(a,b)] = {# ((a,b),[]) #}"
  by (auto simp: ms_of_greek_def adj_msog_def split: accent.splits)
  ultimately show ?thesis
  by (subst greek_less_unfold) (auto intro!: pairwise_imp_mult)
qed

lemma peak_greek_less:
  assumes as: "snd ` set as \<subseteq> under r a" and b': "b' \<in> {[(Grave,b)],[]}"
  and cs: "snd ` set cs \<subseteq> under r a \<union> under r b" and a': "a' \<in> {[(Acute,a)],[]}"
  and bs: "snd ` set bs \<subseteq> under r b"
  shows "(as @ b' @ cs @ a' @ bs, [(Acute,a),(Grave,b)]) \<in> greek_less r"
proof -
  let ?A = "(Acute,a)" and ?B = "(Grave,b)"
  have "(ms_of_greek (as @ b' @ cs @ a' @ bs), ms_of_greek [?A,?B]) \<in> mult (letter_less r <*lex*> greek_less r)"
  proof (intro pairwise_imp_mult)
    (* we distinguish 5 cases depending on where in xs an element e originates *)
    {
      fix e assume "e \<in> set_mset (ms_of_greek as)"
      with as ms_of_greek_elem[of _ _ as]
      have "(adj_msog [] (b' @ cs @ a' @ bs) e, (?A,[?B])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def under_def)
    }
    moreover {
      fix e assume "e \<in> set_mset (ms_of_greek b')"
      with b' singleton_greek_less[OF as] ms_of_greek_elem[of _ _ b']
      have "(adj_msog as (cs @ a' @ bs) e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def ms_of_greek_def)
    }
    moreover {
      fix e assume "e \<in> set_mset (ms_of_greek cs)"
      with cs ms_of_greek_elem[of _ _ cs]
      have "(adj_msog (as @ b') (a' @ bs) e, (?A,[?B])) \<in> letter_less r <*lex*> greek_less r \<or>
            (adj_msog (as @ b') (a' @ bs) e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def under_def)
    }
    moreover {
      fix e assume "e \<in> set_mset (ms_of_greek a')"
      with a' singleton_greek_less[OF bs] ms_of_greek_elem[of _ _ a']
      have "(adj_msog (as @ b' @ cs) bs e, (?A,[?B])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def ms_of_greek_def)
    }
    moreover {
      fix e assume "e \<in> set_mset (ms_of_greek bs)"
      with bs ms_of_greek_elem[of _ _ bs]
      have "(adj_msog (as @ b' @ cs @ a') [] e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def under_def)
    }
    moreover have "ms_of_greek [?A,?B] = {# (?B,[?A]), (?A,[?B]) #}"
    by (simp add: adj_msog_def ms_of_greek_def)
    ultimately show "\<forall>x\<in>set_mset (ms_of_greek (as @ b' @ cs @ a' @ bs)).
      \<exists>y\<in>set_mset (ms_of_greek [?A,?B]). (x, y) \<in> letter_less r <*lex*> greek_less r"
    by (auto simp: msog_append) blast
  qed (auto simp: ms_of_greek_def)
  then show ?thesis by (subst greek_less_unfold) auto
qed

lemma rcliff_greek_less1:
  assumes "trans r" (* unused assumption kept for symmetry with lcliff_greek_less1 *)
  and as: "snd ` set as \<subseteq> under r a \<inter> under r b" and b': "b' \<in> {[(Grave,b)],[]}"
  and cs: "snd ` set cs \<subseteq> under r b" and a': "a' = [(Macron,a)]"
  and bs: "snd ` set bs \<subseteq> under r b"
  shows "(as @ b' @ cs @ a' @ bs, [(Macron,a),(Grave,b)]) \<in> greek_less r"
proof -
  let ?A = "(Macron,a)" and ?B = "(Grave,b)"
  have *: "ms_of_greek [?A,?B] = {#(?B,[?A]), (?A,[])#}" "ms_of_greek [?A] = {#(?A,[])#}"
  by (simp_all add: ms_of_greek_def adj_msog_def)
  then have **: "ms_of_greek [(Macron, a), (Grave, b)] - {#((Macron, a), [])#} \<noteq> {#}"
  by (auto)
  (* we distinguish 5 cases depending on where in xs an element e originates *)
  {
    fix e assume "e \<in> set_mset (ms_of_greek as)"
    with as ms_of_greek_elem[of _ _ as]
    have "(adj_msog [] (b' @ cs @ a' @ bs) e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
    by (cases e) (force simp: adj_msog_def under_def)
  }
  moreover {
    fix e assume "e \<in> set_mset (ms_of_greek b')"
    with b' singleton_greek_less as ms_of_greek_elem[of _ _ b']
    have "(adj_msog as (cs @ a' @ bs) e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
    by (cases e) (fastforce simp: adj_msog_def ms_of_greek_def)
  }
  moreover {
    fix e assume "e \<in> set_mset (ms_of_greek cs)"
    with cs ms_of_greek_elem[of _ _ cs]
    have "(adj_msog (as @ b') (a' @ bs) e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
    by (cases e) (fastforce simp: adj_msog_def under_def)
  }
  moreover {
    fix e assume "e \<in> set_mset (ms_of_greek bs)"
    with bs ms_of_greek_elem[of _ _ bs]
    have "(adj_msog (as @ b' @ cs @ a') [] e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
    by (cases e) (fastforce simp: adj_msog_def under_def)
  }
  moreover have "ms_of_greek [?A,?B] = {# (?B,[?A]), (?A,[]) #}"
  by (simp add: adj_msog_def ms_of_greek_def)
  ultimately have "\<forall>x\<in>set_mset (ms_of_greek (as @ b' @ cs @ a' @ bs) - {#(?A,[])#}).
    \<exists>y\<in>set_mset (ms_of_greek [?A,?B] - {#(?A,[])#}). (x, y) \<in> letter_less r <*lex*> greek_less r"
  unfolding msog_append by (auto simp: a' msog_append ac_simps * adj_msog_single)
  from one_step_implies_mult[OF ** this,of "{#(?A,[])#}"]
  have "(ms_of_greek (as @ b' @ cs @ a' @ bs), ms_of_greek [?A,?B]) \<in> mult (letter_less r <*lex*> greek_less r)"
  unfolding a' msog_append by (auto simp: a' ac_simps * adj_msog_single)
  then show ?thesis
  by (subst greek_less_unfold) auto
qed

lemma rcliff_greek_less2:
  assumes "trans r" (* unused assumption kept for symmetry with lcliff_greek_less2 *)
  and as: "snd ` set as \<subseteq> under r a" and b': "b' \<in> {[(Grave,b)],[]}"
  and cs: "snd ` set cs \<subseteq> under r a \<union> under r b"
  shows "(as @ b' @ cs, [(Macron,a),(Grave,b)]) \<in> greek_less r"
proof -
  let ?A = "(Macron,a)" and ?B = "(Grave,b)"
  have "(ms_of_greek (as @ b' @ cs), ms_of_greek [?A,?B]) \<in> mult (letter_less r <*lex*> greek_less r)"
  proof (intro pairwise_imp_mult)
    (* we distinguish 3 cases depending on where in xs an element e originates *)
    {
      fix e assume "e \<in> set_mset (ms_of_greek as)"
      with as ms_of_greek_elem[of _ _ as]
      have "(adj_msog [] (b' @ cs) e, (?A,[])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def under_def)
    }
    moreover {
      fix e assume "e \<in> set_mset (ms_of_greek b')"
      with b' singleton_greek_less[OF as] ms_of_greek_elem[of _ _ b']
      have "(adj_msog as (cs) e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def ms_of_greek_def)
    }
    moreover {
      fix e assume "e \<in> set_mset (ms_of_greek cs)"
      with cs ms_of_greek_elem[of _ _ cs]
      have "(adj_msog (as @ b') [] e, (?A,[])) \<in> letter_less r <*lex*> greek_less r \<or>
            (adj_msog (as @ b') [] e, (?B,[?A])) \<in> letter_less r <*lex*> greek_less r"
      by (cases e) (fastforce simp: adj_msog_def under_def)
    }
    moreover have *: "ms_of_greek [?A,?B] = {# (?B,[?A]), (?A,[]) #}"
    by (simp add: adj_msog_def ms_of_greek_def)
    ultimately show "\<forall>x\<in>set_mset (ms_of_greek (as @ b' @ cs)).
      \<exists>y\<in>set_mset (ms_of_greek [?A,?B]). (x, y) \<in> letter_less r <*lex*> greek_less r"
    by (auto simp: msog_append adj_msog_single ac_simps *) blast
  qed (auto simp: ms_of_greek_def)
  then show ?thesis by (subst greek_less_unfold) auto
qed

lemma snd_inv_greek [simp]: "snd ` set (inv_greek as) = snd ` set as"
by (force simp: inv_greek_def)

lemma lcliff_greek_less1:
  assumes "trans r"
  and as: "snd ` set as \<subseteq> under r a" and b': "b' = [(Macron,b)]"
  and cs: "snd ` set cs \<subseteq> under r a" and a': "a' \<in> {[(Acute,a)],[]}"
  and bs: "snd ` set bs \<subseteq> under r a \<inter> under r b"
  shows "(as @ b' @ cs @ a' @ bs, [(Acute,a),(Macron,b)]) \<in> greek_less r"
proof -
  have *: "inv_greek [(Acute,a),(Macron,b)] = [(Macron,b),(Grave,a)]" by (simp add: inv_greek_def)
  have "(inv_greek (inv_greek (as @ b' @ cs @ a' @ bs)),
   inv_greek (inv_greek ([(Acute,a),(Macron,b)]))) \<in> greek_less r"
   apply (rule inv_greek_mono[OF \<open>trans r\<close>])
   apply (unfold inv_greek_append append_assoc *)
   apply (insert assms)
   apply (rule rcliff_greek_less1, auto simp: inv_greek_def)
  done
  then show ?thesis by simp
qed

lemma lcliff_greek_less2:
  assumes "trans r"
  and cs: "snd ` set cs \<subseteq> under r a \<union> under r b" and a': "a' \<in> {[(Acute,a)],[]}"
  and bs: "snd ` set bs \<subseteq> under r b"
  shows "(cs @ a' @ bs, [(Acute,a),(Macron,b)]) \<in> greek_less r"
proof -
  have *: "inv_greek [(Acute,a),(Macron,b)] = [(Macron,b),(Grave,a)]" by (simp add: inv_greek_def)
  have "(inv_greek (inv_greek (cs @ a' @ bs)),
    inv_greek (inv_greek ([(Acute,a),(Macron,b)]))) \<in> greek_less r"
   apply (rule inv_greek_mono[OF \<open>trans r\<close>])
   apply (unfold inv_greek_append append_assoc *)
   apply (insert assms)
   apply (rule rcliff_greek_less2, auto simp: inv_greek_def)
  done
  then show ?thesis by simp
qed


subsection \<open>Labeled abstract rewriting\<close>

context
  fixes L R E :: "'b \<Rightarrow> 'a rel"
begin

definition lstep :: "'b letter \<Rightarrow> 'a rel" where
  [simp]: "lstep x = (case x of (a, i) \<Rightarrow> (case a of Acute \<Rightarrow> (L i)\<inverse> | Grave \<Rightarrow> R i | Macron \<Rightarrow> E i))"

fun lconv :: "'b greek \<Rightarrow> 'a rel" where
  "lconv [] = Id"
| "lconv (x # xs) = lstep x O lconv xs"

lemma lconv_append[simp]:
  "lconv (xs @ ys) = lconv xs O lconv ys"
by (induct xs) auto

lemma conversion_join_or_peak_or_cliff:
  obtains (join) as bs cs where "set as \<subseteq> {Grave}" and "set bs \<subseteq> {Macron}" and "set cs \<subseteq> {Acute}"
    and "ds = as @ bs @ cs"
  | (peak) as bs where "ds = as @ ([Acute] @ [Grave]) @ bs"
  | (lcliff) as bs where "ds = as @ ([Acute] @ [Macron]) @ bs"
  | (rcliff) as bs where "ds = as @ ([Macron] @ [Grave]) @ bs"
proof (induct ds arbitrary: thesis)
  case (Cons d ds thesis) note IH = this show ?case
  proof (rule IH(1))
    fix as bs assume "ds = as @ ([Acute] @ [Grave]) @ bs" then show ?case
    using IH(3)[of "d # as" bs] by simp
  next
    fix as bs assume "ds = as @ ([Acute] @ [Macron]) @ bs" then show ?case
    using IH(4)[of "d # as" bs] by simp
  next
    fix as bs assume "ds = as @ ([Macron] @ [Grave]) @ bs" then show ?case
    using IH(5)[of "d # as" bs] by simp
  next
    fix as bs cs assume *: "set as \<subseteq> {Grave}" "set bs \<subseteq> {Macron}" "set cs \<subseteq> {Acute}" "ds = as @ bs @ cs"
    show ?case
    proof (cases d)
      case Grave thus ?thesis using * IH(2)[of "d # as" bs cs] by simp
    next
      case Macron show ?thesis
      proof (cases as)
        case Nil thus ?thesis using * Macron IH(2)[of as "d # bs" cs] by simp
      next
        case (Cons a as) thus ?thesis using * Macron IH(5)[of "[]" "as @ bs @ cs"] by simp
      qed
    next
      case Acute show ?thesis
      proof (cases as)
        case Nil note as = this show ?thesis
        proof (cases bs)
          case Nil thus ?thesis using * as Acute IH(2)[of "[]" "[]" "d # cs"] by simp
        next
          case (Cons b bs) thus ?thesis using * as Acute IH(4)[of "[]" "bs @ cs"] by simp
        qed
      next
        case (Cons a as) thus ?thesis using * Acute IH(3)[of "[]" "as @ bs @ cs"] by simp
      qed
    qed
  qed
qed auto

lemma map_eq_append_split:
  assumes "map f xs = ys1 @ ys2"
  obtains xs1 xs2 where "ys1 = map f xs1" "ys2 = map f xs2" "xs = xs1 @ xs2"
proof (insert assms, induct ys1 arbitrary: xs thesis)
  case (Cons y ys) note IH = this show ?case
  proof (cases xs)
    case (Cons x xs') show ?thesis
    proof (rule IH(1))
      fix xs1 xs2 assume "ys = map f xs1" "ys2 = map f xs2" "xs' = xs1 @ xs2" thus ?thesis
      using Cons IH(2)[of "x # xs1" xs2] IH(3) by simp
    next
      show "map f xs' = ys @ ys2" using Cons IH(3) by simp
    qed
  qed (insert Cons, simp)
qed auto

lemmas map_eq_append_splits = map_eq_append_split map_eq_append_split[OF sym]

abbreviation "conversion' M \<equiv> ((\<Union>i \<in> M. R i) \<union> (\<Union>i \<in> M. E i) \<union> (\<Union>i \<in> M. L i)\<inverse>)\<^sup>*"
abbreviation "valley' M \<equiv>  (\<Union>i \<in> M. R i)\<^sup>* O (\<Union>i \<in> M. E i)\<^sup>* O ((\<Union>i \<in> M. L i)\<inverse>)\<^sup>*"

lemma conversion_to_lconv:
  assumes "(u, v) \<in> conversion' M"
  obtains xs where "snd ` set xs \<subseteq> M" and "(u, v) \<in> lconv xs"
using assms
proof (induct arbitrary: thesis rule: converse_rtrancl_induct)
  case base show ?case using base[of "[]"] by simp
next
  case (step u' x)
  from step(1) obtain p where "snd p \<in> M" and "(u', x) \<in> lstep p"
  by (force split: accent.splits)
  moreover obtain xs where "snd ` set xs \<subseteq> M" "(x, v) \<in> lconv xs" by (rule step(3))
  ultimately show ?case using step(4)[of "p # xs"] by auto
qed

definition lpeak :: "'b rel \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b greek \<Rightarrow> bool" where
  "lpeak r a b xs \<longleftrightarrow> (\<exists>as b' cs a' bs. snd ` set as \<subseteq> under r a \<and> b' \<in> {[(Grave,b)],[]} \<and>
    snd ` set cs \<subseteq> under r a \<union> under r b \<and> a' \<in> {[(Acute,a)],[]} \<and>
    snd ` set bs \<subseteq> under r b \<and> xs = as @ b' @ cs @ a' @ bs)"

definition lcliff :: "'b rel \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b greek \<Rightarrow> bool" where
  "lcliff r a b xs \<longleftrightarrow> (\<exists>as b' cs a' bs. snd ` set as \<subseteq> under r a \<and> b' = [(Macron,b)] \<and>
    snd ` set cs \<subseteq> under r a \<and> a' \<in> {[(Acute,a)],[]} \<and>
    snd ` set bs \<subseteq> under r a \<inter> under r b \<and> xs = as @ b' @ cs @ a' @ bs) \<or>
    (\<exists>cs a' bs. snd ` set cs \<subseteq> under r a \<union> under r b \<and> a' \<in> {[(Acute,a)],[]} \<and>
    snd ` set bs \<subseteq> under r b \<and> xs = cs @ a' @ bs)"
    
definition rcliff :: "'b rel \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> 'b greek \<Rightarrow> bool" where
  "rcliff r a b xs \<longleftrightarrow> (\<exists>as b' cs a' bs. snd ` set as \<subseteq> under r a \<inter> under r b \<and> b' \<in> {[(Grave,b)],[]} \<and>
    snd ` set cs \<subseteq> under r b \<and> a' = [(Macron,a)] \<and>
    snd ` set bs \<subseteq> under r b \<and> xs = as @ b' @ cs @ a' @ bs) \<or>
    (\<exists>as b' cs. snd ` set as \<subseteq> under r a \<and> b' \<in> {[(Grave,b)],[]} \<and>
    snd ` set cs \<subseteq> under r a \<union> under r b \<and> xs = as @ b' @ cs)"

lemma dd_commute_modulo_conv[case_names wf trans peak lcliff rcliff]:
  assumes "wf r" and "trans r"
  and pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow> \<exists>xs. lpeak r a b xs \<and> (t, u) \<in> lconv xs"
  and lc: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> E b \<Longrightarrow> \<exists>xs. lcliff r a b xs \<and> (t, u) \<in> lconv xs"
  and rc: "\<And>a b s t u. (s, t) \<in> (E a)\<inverse> \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow> \<exists>xs. rcliff r a b xs \<and> (t, u) \<in> lconv xs"
  shows "conversion' UNIV \<subseteq> valley' UNIV"
proof (intro subrelI)
  fix u v
  assume "(u,v) \<in> conversion' UNIV"
  then obtain xs where "(u, v) \<in> lconv xs" by (auto intro: conversion_to_lconv[of u v])
  then show "(u, v) \<in> valley' UNIV"
  proof (induct xs rule: wf_induct[of "greek_less r"])
    case 1 thus ?case using wf_greek_less[OF \<open>wf r\<close> \<open>trans r\<close>] .
  next
    case (2 xs) show ?case
    proof (rule conversion_join_or_peak_or_cliff[of "map fst xs"])
      fix as bs cs
      assume *: "set as \<subseteq> {Grave}" "set bs \<subseteq> {Macron}" "set cs \<subseteq> {Acute}" "map fst xs = as @ bs @ cs"
      then show "(u, v) \<in> valley' UNIV"
      proof (elim map_eq_append_splits)
        fix as' bs' cs' bcs'
        assume as: "set as \<subseteq> {Grave}" "as = map fst as'" and
          bs: "set bs \<subseteq> {Macron}" "bs = map fst bs'" and
          cs: "set cs \<subseteq> {Acute}" "cs = map fst cs'" and
          xs: "xs = as' @ bcs'" "bcs' = bs' @ cs'"
        from as(1)[unfolded as(2)] have as': "\<And>x y. (x,y) \<in> lconv as' \<Longrightarrow> (x,y) \<in> (\<Union>a. R a)\<^sup>*"
        proof (induct as')
          case (Cons x' xs)
          have "\<And>x y z i. (x,y) \<in> R i \<Longrightarrow> (y,z) \<in> (\<Union>a. R a)\<^sup>* \<Longrightarrow> (x,z) \<in> (\<Union>a. R a)\<^sup>*"
          by (rule rtrancl_trans) auto
          with Cons show ?case by auto
        qed simp
        from bs(1)[unfolded bs(2)] have bs': "\<And>x y. (x,y) \<in> lconv bs' \<Longrightarrow> (x,y) \<in> (\<Union>a. E a)\<^sup>*"
        proof (induct bs')
          case (Cons x' xs)
          have "\<And>x y z i. (x,y) \<in> E i \<Longrightarrow> (y,z) \<in> (\<Union>a. E a)\<^sup>* \<Longrightarrow> (x,z) \<in> (\<Union>a. E a)\<^sup>*"
          by (rule rtrancl_trans) auto 
          with Cons show ?case by auto
        qed simp
        from cs(1)[unfolded cs(2)] have cs': "\<And>x y. (x,y) \<in> lconv cs' \<Longrightarrow> (x,y) \<in> ((\<Union>a. L a)\<inverse>)\<^sup>*"
        proof (induct cs')
          case (Cons x' xs)
          have "\<And>x y z i. (x,y) \<in> (L i)\<inverse> \<Longrightarrow> (y,z) \<in> ((\<Union>a. L a)\<inverse>)\<^sup>* \<Longrightarrow> (x,z) \<in> ((\<Union>a. L a)\<inverse>)\<^sup>*"
          by (rule rtrancl_trans) auto 
          with Cons show ?case by auto
        qed simp
        from 2(2) as' bs' cs' show "(u, v) \<in> valley' UNIV"
        unfolding xs lconv_append by auto (meson relcomp.simps) 
      qed
    next
      fix as bs assume *: "map fst xs = as @ ([Acute] @ [Grave]) @ bs"
      {
        fix p a b q t' s' u'
        assume xs: "xs = p @ [(Acute,a),(Grave,b)] @ q" and p: "(u,t') \<in> lconv p"
          and a: "(s',t') \<in> L a" and b: "(s',u') \<in> R b" and q: "(u',v) \<in> lconv q"
        obtain js where lp: "lpeak r a b js" and js: "(t',u') \<in> lconv js" using pk[OF a b] by auto
        from lp have "(js, [(Acute,a),(Grave,b)]) \<in> greek_less r"
        unfolding lpeak_def using peak_greek_less[of _ r a _ b] by fastforce
        then have "(p @ js @ q, xs) \<in> greek_less r" unfolding xs
        by (intro greek_less_app_mono1 greek_less_app_mono2 \<open>trans r\<close>) auto
        moreover have "(u, v) \<in> lconv (p @ js @ q)"
        using p q js by auto
        ultimately have "(u, v) \<in> valley' UNIV" using 2(1) by blast
      }
      with * show "(u, v) \<in> valley' UNIV" using 2(2)
      by (auto elim!: map_eq_append_splits relcompEpair simp del: append.simps) simp
    next
      fix as bs assume *: "map fst xs = as @ ([Acute] @ [Macron]) @ bs"
      {
        fix p a b q t' s' u'
        assume xs: "xs = p @ [(Acute,a),(Macron,b)] @ q" and p: "(u,t') \<in> lconv p"
          and a: "(s',t') \<in> L a" and b: "(s',u') \<in> E b" and q: "(u',v) \<in> lconv q"
        obtain js where lp: "lcliff r a b js" and js: "(t',u') \<in> lconv js" using lc[OF a b] by auto
        from lp have "(js, [(Acute,a),(Macron,b)]) \<in> greek_less r"
        unfolding lcliff_def
        using lcliff_greek_less1[OF \<open>trans r\<close>, of _ a _ b] lcliff_greek_less2[OF \<open>trans r\<close>, of _ a b]
        by fastforce
        then have "(p @ js @ q, xs) \<in> greek_less r" unfolding xs
        by (intro greek_less_app_mono1 greek_less_app_mono2 \<open>trans r\<close>) auto
        moreover have "(u, v) \<in> lconv (p @ js @ q)"
        using p q js by auto
        ultimately have "(u, v) \<in> valley' UNIV" using 2(1) by blast
      }
      with * show "(u, v) \<in> valley' UNIV" using 2(2)
      by (auto elim!: map_eq_append_splits relcompEpair simp del: append.simps) simp
    next
      fix as bs assume *: "map fst xs = as @ ([Macron] @ [Grave]) @ bs"
      {
        fix p a b q t' s' u'
        assume xs: "xs = p @ [(Macron,a),(Grave,b)] @ q" and p: "(u,t') \<in> lconv p"
          and a: "(s',t') \<in> (E a)\<inverse>" and b: "(s',u') \<in> R b" and q: "(u',v) \<in> lconv q"
        obtain js where lp: "rcliff r a b js" and js: "(t',u') \<in> lconv js" using rc[OF a b] by auto
        from lp have "(js, [(Macron,a),(Grave,b)]) \<in> greek_less r"
        unfolding rcliff_def
        using rcliff_greek_less1[OF \<open>trans r\<close>, of _ a b] rcliff_greek_less2[OF \<open>trans r\<close>, of _ a _ b]
        by fastforce
        then have "(p @ js @ q, xs) \<in> greek_less r" unfolding xs
        by (intro greek_less_app_mono1 greek_less_app_mono2 \<open>trans r\<close>) auto
        moreover have "(u, v) \<in> lconv (p @ js @ q)"
        using p q js by auto
        ultimately have "(u, v) \<in> valley' UNIV" using 2(1) by blast
      }
      with * show "(u, v) \<in> valley' UNIV" using 2(2)
      by (auto elim!: map_eq_append_splits relcompEpair simp del: append.simps) simp
    qed
  qed
qed


section \<open>Results\<close>

subsection \<open>Church-Rosser modulo\<close>

text \<open>Decreasing diagrams for Church-Rosser modulo, commutation version.\<close>

lemma dd_commute_modulo[case_names wf trans peak lcliff rcliff]:
  assumes "wf r" and "trans r"
  and pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow>
    (t, u) \<in> conversion' (under r a) O (R b)\<^sup>= O conversion' (under r a \<union> under r b) O
      ((L a)\<inverse>)\<^sup>= O conversion' (under r b)"
  and lc: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> E b \<Longrightarrow>
    (t, u) \<in> conversion' (under r a) O E b O conversion' (under r a) O
      ((L a)\<inverse>)\<^sup>= O conversion' (under r a \<inter> under r b) \<or>
    (t, u) \<in> conversion' (under r a \<union> under r b) O ((L a )\<inverse>)\<^sup>= O conversion' (under r b)"
  and rc: "\<And>a b s t u. (s, t) \<in> (E a)\<inverse> \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow>
    (t, u) \<in> conversion' (under r a \<inter> under r b) O (R b)\<^sup>= O conversion' (under r b) O
      E a O conversion' (under r b) \<or>
    (t, u) \<in> conversion' (under r a) O (R b)\<^sup>= O conversion' (under r a \<union> under r b)"
  shows "conversion' UNIV \<subseteq> valley' UNIV"
proof (cases rule: dd_commute_modulo_conv[of r])
  case (peak a b s t u)
  {
    fix w x y z
    assume "(t, w) \<in> conversion' (under r a)"
    from conversion_to_lconv[OF this]
    obtain as where "snd ` set as \<subseteq> under r a" "(t, w) \<in> lconv as" by auto
    moreover assume "(w, x) \<in> (R b)\<^sup>="
    then obtain b' where "b' \<in> {[(Grave,b)],[]}" "(w, x) \<in> lconv b'" by fastforce
    moreover assume "(x, y) \<in> conversion' (under r a \<union> under r b)"
    from conversion_to_lconv[OF this]
    obtain cs where "snd ` set cs \<subseteq> under r a \<union> under r b" "(x, y) \<in> lconv cs" by auto
    moreover assume "(y, z) \<in> ((L a)\<inverse>)\<^sup>="
    then obtain a' where "a' \<in> {[(Acute,a)],[]}" "(y, z) \<in> lconv a'" by fastforce
    moreover assume "(z, u) \<in> conversion' (under r b)"
    from conversion_to_lconv[OF this]
    obtain bs where "snd ` set bs \<subseteq> under r b" "(z, u) \<in> lconv bs" by auto
    ultimately have "\<exists>xs. lpeak r a b xs \<and> (t, u) \<in> lconv xs"
    by (intro exI[of _ "as @ b' @ cs @ a' @ bs"], unfold lconv_append lpeak_def) blast
  }
  then show ?case using pk[OF peak] by blast
next
  case (lcliff a b s t u)
  {
    fix w x y z
    assume "(t, w) \<in> conversion' (under r a)"
    from conversion_to_lconv[OF this]
    obtain as where "snd ` set as \<subseteq> under r a" "(t, w) \<in> lconv as" by auto
    moreover assume "(w, x) \<in> E b"
    then obtain b' where "b' = [(Macron,b)]" "(w, x) \<in> lconv b'" by fastforce
    moreover assume "(x, y) \<in> conversion' (under r a)"
    from conversion_to_lconv[OF this]
    obtain cs where "snd ` set cs \<subseteq> under r a" "(x, y) \<in> lconv cs" by auto
    moreover assume "(y, z) \<in> ((L a)\<inverse>)\<^sup>="
    then obtain a' where "a' \<in> {[(Acute,a)],[]}" "(y, z) \<in> lconv a'" by fastforce
    moreover assume "(z, u) \<in> conversion' (under r a \<inter> under r b)"
    from conversion_to_lconv[OF this]
    obtain bs where "snd ` set bs \<subseteq> under r a \<inter> under r b" "(z, u) \<in> lconv bs" by auto
    ultimately have "\<exists>xs. lcliff r a b xs \<and> (t, u) \<in> lconv xs"
    by (intro exI[of _ "as @ b' @ cs @ a' @ bs"], unfold lconv_append lcliff_def) blast
  }
  moreover {
    fix w x
    assume "(t, w) \<in> conversion' (under r a \<union> under r b)"
    from conversion_to_lconv[OF this]
    obtain cs where "snd ` set cs \<subseteq> under r a \<union> under r b" "(t, w) \<in> lconv cs" by auto
    moreover assume "(w, x) \<in> ((L a)\<inverse>)\<^sup>="
    then obtain a' where "a' \<in> {[(Acute,a)],[]}" "(w, x) \<in> lconv a'" by fastforce
    moreover assume "(x, u) \<in> conversion' (under r b)"
    from conversion_to_lconv[OF this]
    obtain bs where "snd ` set bs \<subseteq> under r b" "(x, u) \<in> lconv bs" by auto
    ultimately have "\<exists>xs. lcliff r a b xs \<and> (t, u) \<in> lconv xs"
    by (intro exI[of _ "cs @ a' @ bs"], unfold lconv_append lcliff_def) blast
  }
  ultimately show ?case using lc[OF lcliff] by blast
next
  case (rcliff a b s t u)
  {
    fix w x y z
    assume "(t, w) \<in> conversion' (under r a \<inter> under r b)"
    from conversion_to_lconv[OF this]
    obtain as where "snd ` set as \<subseteq> under r a \<inter> under r b" "(t, w) \<in> lconv as" by auto
    moreover assume "(w, x) \<in> (R b)\<^sup>="
    then obtain b' where "b' \<in> {[(Grave,b)],[]}" "(w, x) \<in> lconv b'" by fastforce
    moreover assume "(x, y) \<in> conversion' (under r b)"
    from conversion_to_lconv[OF this]
    obtain cs where "snd ` set cs \<subseteq> under r b" "(x, y) \<in> lconv cs" by auto
    moreover assume "(y, z) \<in> E a"
    then obtain a' where "a' = [(Macron,a)]" "(y, z) \<in> lconv a'" by fastforce
    moreover assume "(z, u) \<in> conversion' (under r b)"
    from conversion_to_lconv[OF this]
    obtain bs where "snd ` set bs \<subseteq> under r b" "(z, u) \<in> lconv bs" by auto
    ultimately have "\<exists>xs. rcliff r a b xs \<and> (t, u) \<in> lconv xs"
    by (intro exI[of _ "as @ b' @ cs @ a' @ bs"], unfold lconv_append rcliff_def) blast
  }
  moreover {
    fix w x
    assume "(t, w) \<in> conversion' (under r a)"
    from conversion_to_lconv[OF this]
    obtain as where "snd ` set as \<subseteq> under r a" "(t, w) \<in> lconv as" by auto
    moreover assume "(w, x) \<in> (R b)\<^sup>="
    then obtain b' where "b' \<in> {[(Grave,b)],[]}" "(w, x) \<in> lconv b'" by fastforce
    moreover assume "(x, u) \<in> conversion' (under r a \<union> under r b)"
    from conversion_to_lconv[OF this]
    obtain cs where "snd ` set cs \<subseteq> under r a \<union> under r b" "(x, u) \<in> lconv cs" by auto
    ultimately have "\<exists>xs. rcliff r a b xs \<and> (t, u) \<in> lconv xs"
    by (intro exI[of _ "as @ b' @ cs"], unfold lconv_append rcliff_def) blast
  }
  ultimately show ?case using rc[OF rcliff] by blast
qed fact+

end (* context *)

text \<open>Decreasing diagrams for Church-Rosser modulo.\<close>

lemma dd_cr_modulo[case_names wf trans symE peak cliff]:
  assumes "wf r" and "trans r" and E: "\<And>i. sym (E i)"
  and pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> L b \<Longrightarrow>
    (t, u) \<in> conversion' L L E (under r a) O (L b)\<^sup>= O conversion' L L E (under r a \<union> under r b) O
      ((L a)\<inverse>)\<^sup>= O conversion' L L E (under r b)"
  and cl: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> E b \<Longrightarrow>
    (t, u) \<in> conversion' L L E (under r a) O E b O conversion' L L E (under r a) O
      ((L a)\<inverse>)\<^sup>= O conversion' L L E (under r a \<inter> under r b) \<or>
    (t, u) \<in> conversion' L L E (under r a \<union> under r b) O ((L a )\<inverse>)\<^sup>= O conversion' L L E (under r b)"
  shows "conversion' L L E UNIV \<subseteq> valley' L L E UNIV"
proof (induct rule: dd_commute_modulo[of r])
  note E' = E[unfolded sym_conv_converse_eq]
  case (rcliff a b s t u) show ?case
  using cl[OF rcliff(2) rcliff(1)[unfolded E'], unfolded converse_iff[of t u,symmetric]]
  by (auto simp only: ac_simps E' converse_inward)
qed fact+

subsection \<open>Commutation and confluence\<close>

abbreviation "conversion'' L R M \<equiv> ((\<Union>i \<in> M. R i) \<union> (\<Union>i \<in> M. L i)\<inverse>)\<^sup>*"
abbreviation "valley'' L R M \<equiv> (\<Union>i \<in> M. R i)\<^sup>* O ((\<Union>i \<in> M. L i)\<inverse>)\<^sup>*"

text \<open>Decreasing diagrams for commutation.\<close>

lemma dd_commute[case_names wf trans peak]:
  assumes "wf r" and "trans r"
  and pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow>
    (t, u) \<in> conversion'' L R (under r a) O (R b)\<^sup>= O conversion'' L R (under r a \<union> under r b) O
      ((L a)\<inverse>)\<^sup>= O conversion'' L R (under r b)"
  shows "commute (\<Union>i. L i) (\<Union>i. R i)"
proof -
  have "((\<Union>i. L i)\<inverse>)\<^sup>* O (\<Union>i. R i)\<^sup>* \<subseteq> conversion'' L R UNIV" by regexp
  also have "\<dots> \<subseteq> valley'' L R UNIV"
  using dd_commute_modulo[OF assms(1,2), of L R "\<lambda>_. {}"] pk by auto
  finally show ?thesis by (simp only: commute_def)
qed

text \<open>Decreasing diagrams for confluence.\<close>

lemmas dd_cr[case_names wf trans peak] =
  dd_commute[of _ L L for L, unfolded CR_iff_self_commute[symmetric]]


subsection \<open>Extended decreasing diagrams\<close>

context
  fixes r q :: "'b rel"
  assumes "wf r" and "trans r" and "trans q" and "refl q" and compat: "r O q \<subseteq> r"
begin

private abbreviation (input) down :: "('b \<Rightarrow> 'a rel) \<Rightarrow> ('b \<Rightarrow> 'a rel)" where
  "down L \<equiv> \<lambda>i. \<Union>j \<in> under q i. L j"

private lemma Union_down: "(\<Union>i. down L i) = (\<Union>i. L i)"
using \<open>refl q\<close> by (auto simp: refl_on_def under_def)

text \<open>Extended decreasing diagrams for commutation.\<close>

lemma edd_commute[case_names wf transr transq reflq compat peak]:
  assumes pk: "\<And>a b s t u. (s, t) \<in> L a \<Longrightarrow> (s, u) \<in> R b \<Longrightarrow>
    (t, u) \<in> conversion'' L R (under r a) O (down R b)\<^sup>= O conversion'' L R (under r a \<union> under r b) O
      ((down L a)\<inverse>)\<^sup>= O conversion'' L R (under r b)"
  shows "commute (\<Union>i. L i) (\<Union>i. R i)"
unfolding Union_down[of L, symmetric] Union_down[of R, symmetric]
proof (induct rule: dd_commute[of r "down L" "down R"])
  case (peak a b s t u)
  then obtain a' b' where a': "(a', a) \<in> q" "(s, t) \<in> L a'" and b': "(b', b) \<in> q" "(s, u) \<in> R b'"
  by (auto simp: under_def)
  have "\<And>a' a. (a',a) \<in> q \<Longrightarrow> under r a' \<subseteq> under r a" using compat by (auto simp: under_def)
  then have aux1: "\<And>a' a L. (a',a) \<in> q \<Longrightarrow> (\<Union>i \<in> under r a'. L i) \<subseteq> (\<Union>i \<in> under r a. L i)" by auto
  have aux2: "\<And>a' a L. (a',a) \<in> q \<Longrightarrow> down L a' \<subseteq> down L a" 
    using \<open>trans q\<close> by (auto simp: under_def trans_def)
  have aux3: "\<And>a L. (\<Union>i \<in> under r a. L i) \<subseteq> (\<Union>i \<in> under r a. down L i)"
    using \<open>refl q\<close> by (auto simp: under_def refl_on_def)
  from aux1[OF a'(1), of L] aux1[OF a'(1), of R] aux2[OF a'(1), of L]
       aux1[OF b'(1), of L] aux1[OF b'(1), of R] aux2[OF b'(1), of R]
       aux3[of L] aux3[of R]
  show ?case
  by (intro subsetD[OF _ pk[OF \<open>(s, t) \<in> L a'\<close> \<open>(s, u) \<in> R b'\<close>]], unfold UN_Un)
     (intro relcomp_mono rtrancl_mono Un_mono iffD2[OF converse_mono]; fast)
qed fact+

text \<open>Extended decreasing diagrams for confluence.\<close>

lemmas edd_cr[case_names wf transr transq reflq compat peak] =
  edd_commute[of L L for L, unfolded CR_iff_self_commute[symmetric]]

end (* context *)

end (* Decreasing_Diagrams_II *)
