(*  Author:  Gertrud Bauer, Tobias Nipkow  *)

section\<open>Properties of Face Division\<close>

theory FaceDivisionProps
imports Plane EnumeratorProps
begin

subsection\<open>Finality\<close>

(********************* makeFaceFinal ****************************)

lemma vertices_makeFaceFinal: "vertices(makeFaceFinal f g) = vertices g"
by(induct g)(simp add:vertices_graph_def makeFaceFinal_def)

lemma edges_makeFaceFinal: "\<E> (makeFaceFinal f g) = \<E> g"
proof -
  { fix fs
    have "(\<Union>\<^bsub>f\<in>set (makeFaceFinalFaceList f fs)\<^esub> edges f) = (\<Union>\<^bsub>f\<in> set fs\<^esub> edges f)"
    apply(unfold makeFaceFinalFaceList_def)
    apply(induct f)
    by(induct fs) simp_all }
  thus ?thesis by(simp add:edges_graph_def makeFaceFinal_def)
qed


lemma in_set_repl_setFin:
  "f \<in> set fs \<Longrightarrow> final f \<Longrightarrow> f \<in> set (replace f' [setFinal f'] fs)"
by (induct fs) auto

lemma in_set_repl:  "f \<in> set fs \<Longrightarrow> f \<noteq> f' \<Longrightarrow> f \<in> set (replace f' fs' fs)"
by (induct fs) auto

lemma makeFaceFinals_preserve_finals:
  "f \<in> set (finals g) \<Longrightarrow> f \<in> set (finals (makeFaceFinal f' g))"
by (induct g)
   (simp add:makeFaceFinal_def finals_def makeFaceFinalFaceList_def
             in_set_repl_setFin)


lemma len_faces_makeFaceFinal[simp]:
 "|faces (makeFaceFinal f g)| = |faces g|"
by(simp add:makeFaceFinal_def makeFaceFinalFaceList_def)

lemma len_finals_makeFaceFinal:
 "f \<in> \<F> g \<Longrightarrow> \<not> final f \<Longrightarrow> |finals (makeFaceFinal f g)| = |finals g| + 1"
by(simp add:makeFaceFinal_def finals_def makeFaceFinalFaceList_def
            length_filter_replace1)

lemma len_nonFinals_makeFaceFinal:
 "\<lbrakk> \<not> final f; f \<in> \<F> g\<rbrakk>
  \<Longrightarrow> |nonFinals (makeFaceFinal f g)| = |nonFinals g| - 1"
by(simp add:makeFaceFinal_def nonFinals_def makeFaceFinalFaceList_def
            length_filter_replace2)


lemma set_finals_makeFaceFinal[simp]: "distinct(faces g) \<Longrightarrow> f \<in> \<F> g \<Longrightarrow>
  set(finals (makeFaceFinal f g)) = insert (setFinal f) (set(finals g))"
by(auto simp:finals_def makeFaceFinal_def makeFaceFinalFaceList_def
                distinct_set_replace)


lemma splitFace_preserve_final:
  "f \<in> set (finals g) \<Longrightarrow> \<not> final f' \<Longrightarrow>
   f \<in> set (finals (snd (snd (splitFace g i j f' ns))))"
  by (induct g) (auto simp add: splitFace_def finals_def split_def
                      intro: in_set_repl)

lemma splitFace_nonFinal_face:
  "\<not> final (fst (snd (splitFace g i j f' ns)))"
  by (simp add: splitFace_def split_def split_face_def)


lemma subdivFace'_preserve_finals:
  "\<And>n i f' g. f \<in> set (finals g) \<Longrightarrow>  \<not> final f' \<Longrightarrow>
   f \<in> set (finals (subdivFace' g f' i n is))"
proof (induct "is")
  case Nil then show ?case by(simp add:makeFaceFinals_preserve_finals)
next
  case (Cons j "js") then show ?case
  proof (cases j)
    case None with Cons show ?thesis by simp
  next
    case (Some sj)
    with Cons show ?thesis
      by (auto simp: splitFace_preserve_final splitFace_nonFinal_face split_def)
  qed
qed

lemma subdivFace_pres_finals:
  "f \<in> set (finals g) \<Longrightarrow> \<not> final f' \<Longrightarrow>
   f \<in> set (finals (subdivFace g f' is))"
by(simp add:subdivFace_def subdivFace'_preserve_finals)


declare Nat.diff_is_0_eq' [simp del]

(********************* section is_prefix ****************************)
subsection \<open>\<open>is_prefix\<close>\<close>

definition is_prefix :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_prefix ls vs \<equiv>  (\<exists> bs. vs = ls @ bs)"

lemma is_prefix_add:
  "is_prefix ls vs \<Longrightarrow> is_prefix (as @ ls) (as @ vs)" by (simp add: is_prefix_def)

lemma is_prefix_hd[simp]:
  "is_prefix [l] vs = (l = hd vs \<and> vs \<noteq> [])"
  apply (rule iffI) apply (auto simp: is_prefix_def)
  apply (intro exI) apply (subgoal_tac "vs = hd vs # tl vs") apply assumption by auto

lemma is_prefix_f[simp]:
  "is_prefix (a#as) (a#vs) = is_prefix as vs" by (auto simp: is_prefix_def)

lemma splitAt_is_prefix: "ram \<in> set vs \<Longrightarrow> is_prefix (fst (splitAt ram vs) @ [ram]) vs"
by (auto dest!: splitAt_ram simp: is_prefix_def)


(******************** section is_sublist *********************************)
subsection \<open>\<open>is_sublist\<close>\<close>

definition is_sublist :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_sublist ls vs \<equiv>  (\<exists> as bs. vs = as @ ls @ bs)"

lemma is_prefix_sublist:
  "is_prefix ls vs \<Longrightarrow> is_sublist ls vs" by (auto simp: is_prefix_def is_sublist_def)

lemma is_sublist_trans: "is_sublist as bs \<Longrightarrow> is_sublist bs cs \<Longrightarrow> is_sublist as cs"
  apply (simp add: is_sublist_def) apply (elim exE)
  apply (subgoal_tac "cs = (asaa @ asa) @ as @ (bsa @ bsaa)")
  apply (intro exI)  apply assumption by force

lemma is_sublist_add: "is_sublist as bs \<Longrightarrow> is_sublist as (xs @ bs @ ys)"
  apply (simp add: is_sublist_def) apply (elim exE)
  apply (subgoal_tac "xs @ bs @ ys = (xs @ asa) @ as @ (bsa @ ys)")
  apply (intro exI) apply assumption by auto


lemma is_sublist_rec:
"is_sublist xs ys =
 (if length xs > length ys then False else
  if xs = take (length xs) ys then True else is_sublist xs (tl ys))"
proof (simp add:is_sublist_def, goal_cases)
  case 1 show ?case
  proof (standard, goal_cases)
    case 1 show ?case
    proof (standard, goal_cases)
      case xs: 1
      show ?case
      proof (standard, goal_cases)
        case 1 show ?case by auto
      next
        case 2 show ?case
        proof (standard, goal_cases)
          case 1
          have "ys = take |xs| ys @ drop |xs| ys" by simp
          also have "\<dots> = [] @ xs @ drop |xs| ys" by(simp add:xs[symmetric])
          finally show ?case by blast
        qed
      qed
    qed
  next
    case 2 show ?case
    proof (standard, goal_cases)
      case xs_neq: 1
      show ?case
      proof (standard, goal_cases)
        case 1 show ?case by auto
      next
        case 2 show ?case
        proof (standard, goal_cases)
          case not_less: 1 show ?case
          proof (standard, goal_cases)
            case 1
            then obtain as bs where ys: "ys = as @ xs @ bs" by blast
            have "as \<noteq> []" using xs_neq ys by auto
            then obtain a as' where "as = a # as'"
              by (simp add:neq_Nil_conv) blast
            hence "tl ys = as' @ xs @ bs" by(simp add:ys)
            thus ?case by blast
          next
            case 2
            then obtain as bs where ys: "tl ys = as @ xs @ bs" by blast
            have "ys \<noteq> []" using xs_neq not_less by auto
            then obtain y ys' where "ys = y # ys'"
              by (simp add:neq_Nil_conv) blast
            hence "ys = (y#as) @ xs @ bs" using ys by simp
            thus ?case by blast
          qed
        qed
      qed
    qed
  qed
qed


lemma not_sublist_len[simp]:
 "|ys| < |xs| \<Longrightarrow> \<not> is_sublist xs ys"
by(simp add:is_sublist_rec)

lemma is_sublist_simp[simp]: "a \<noteq> v \<Longrightarrow> is_sublist (a#as) (v#vs) = is_sublist (a#as) vs"
proof
  assume av: "a \<noteq> v" and subl: "is_sublist (a # as) (v # vs)"
  then obtain rs ts where vvs: "v#vs = rs @ (a # as) @ ts" by (auto simp: is_sublist_def)
  with av have "rs \<noteq> []" by auto
  with vvs have "tl (v#vs) = tl rs @ a # as @ ts" by auto
  then have "vs = tl rs @ a # as @ ts" by auto
  then show "is_sublist (a # as) vs" by (auto simp: is_sublist_def)
next
  assume av: "a \<noteq> v" and subl: "is_sublist (a # as) vs"
  then show "is_sublist (a # as) (v # vs)" apply (auto simp: is_sublist_def)  apply (intro exI)
    apply (subgoal_tac "v # asa @ a # as @ bs = (v # asa) @ a # as @ bs") apply assumption by auto
qed

lemma is_sublist_id[simp]: "is_sublist vs vs" apply (auto simp: is_sublist_def) apply (intro exI)
  apply (subgoal_tac "vs = [] @ vs @ []") by (assumption) auto

lemma is_sublist_in: "is_sublist (a#as) vs \<Longrightarrow> a \<in> set vs" by (auto simp: is_sublist_def)

lemma is_sublist_in1: "is_sublist [x,y] vs \<Longrightarrow> y \<in> set vs" by (auto simp: is_sublist_def)

lemma is_sublist_notlast[simp]: "distinct vs \<Longrightarrow> x = last vs \<Longrightarrow> \<not> is_sublist [x,y] vs"
proof
  assume dvs: "distinct vs" and xl: "x = last vs" and subl:"is_sublist [x, y] vs"
  then obtain rs ts where vs: "vs = rs @ x # y # ts" by (auto simp: is_sublist_def)
  define as where "as = rs @ [x]"
  define bs where "bs = y # ts"
  then have bsne: "bs \<noteq> []" by auto
  from as_def bs_def have vs2: "vs = as @ bs" using vs by auto
  with as_def have xas: "x \<in> set as" by auto
  from bsne vs2 have "last vs = last bs" by auto
  with xl have "x = last bs" by auto
  with bsne have "bs = (butlast bs) @ [x]" by auto
  then have "x \<in> set bs" by (induct bs) auto
  with xas vs2 dvs show False by auto
qed

lemma is_sublist_nth1: "is_sublist [x,y] ls \<Longrightarrow>
  \<exists> i j. i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y \<and> Suc i = j"
proof -
  assume subl: "is_sublist [x,y] ls"
  then obtain as bs where "ls = as @ x # y # bs" by (auto simp: is_sublist_def)
  then have "(length as) < length ls \<and> (Suc (length as)) < length ls \<and> ls!(length as) = x
       \<and> ls!(Suc (length as)) = y \<and> Suc (length as) = (Suc (length as))"
    apply auto apply hypsubst_thin apply (induct as) by auto
  then show ?thesis by auto
qed

lemma is_sublist_nth2: "\<exists> i j. i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y \<and> Suc i = j \<Longrightarrow>
 is_sublist [x,y] ls "
proof -
  assume "\<exists> i j. i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y \<and> Suc i = j"
  then obtain i j where vors: "i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y \<and> Suc i = j" by auto
  then have "ls = take (Suc (Suc i)) ls @ drop (Suc (Suc i)) ls" by auto
  with vors have "ls = take (Suc i) ls @ [ls! (Suc i)] @ drop (Suc (Suc i)) ls"
    by (auto simp: take_Suc_conv_app_nth)
  with vors have "ls = take i ls @ [ls!i] @ [ls! (Suc i)] @ drop (Suc (Suc i)) ls"
   by (auto simp: take_Suc_conv_app_nth)
  with vors show ?thesis by (auto simp: is_sublist_def)
qed

lemma is_sublist_tl: "is_sublist (a # as) vs \<Longrightarrow> is_sublist as vs" apply (simp add: is_sublist_def)
  apply (elim exE) apply (intro exI)
  apply (subgoal_tac "vs = (asa @ [a]) @ as @ bs") apply assumption by auto

lemma is_sublist_hd: "is_sublist (a # as) vs \<Longrightarrow> is_sublist [a] vs" apply (simp add: is_sublist_def) by auto

lemma is_sublist_hd_eq[simp]: "(is_sublist [a] vs) = (a \<in> set vs)" apply (rule_tac iffI)
  apply (simp add: is_sublist_def) apply force
  apply (simp add: is_sublist_def) apply (induct vs) apply force apply (case_tac "a = aa") apply force
  apply (subgoal_tac "a \<in> set vs") apply simp apply (elim exE) apply (intro exI)
  apply (subgoal_tac "aa # vs = (aa # as) @ a # bs") apply (assumption) by auto

lemma is_sublist_distinct_prefix:
  "is_sublist (v#as) (v # vs) \<Longrightarrow> distinct (v # vs) \<Longrightarrow> is_prefix as vs"
proof -
  assume d:  "distinct (v # vs)" and subl: "is_sublist (v # as) (v # vs)"
  from subl obtain rs ts where v_vs: "v # vs = rs @ (v # as) @ ts" by (simp add: is_sublist_def) auto
  from d have v: "v \<notin> set vs" by auto
  then have "\<not> is_sublist (v # as) vs" by (auto dest: is_sublist_hd)
  with v_vs have "rs = []" apply (cases rs) by (auto simp: is_sublist_def)
  with v_vs show "is_prefix as vs" by (auto simp: is_prefix_def)
qed

lemma is_sublist_distinct[intro]:
  "is_sublist as vs \<Longrightarrow> distinct vs \<Longrightarrow> distinct as" by (auto simp: is_sublist_def)

lemma is_sublist_y_hd: "distinct vs \<Longrightarrow> y = hd vs \<Longrightarrow> \<not> is_sublist [x,y] vs"
proof
  assume d: "distinct vs" and yh: "y = hd vs" and subl: "is_sublist [x, y] vs"
  then obtain rs ts where vs: "vs = rs @ x # y # ts" by (auto simp: is_sublist_def)
  define as where "as = rs @ [x]"
  then have asne: "as \<noteq> []" by auto
  define bs where "bs = y # ts"
  then have bsne: "bs \<noteq> []" by auto
  from as_def bs_def have vs2: "vs = as @ bs" using vs by auto
  from bs_def have xbs: "y \<in> set bs" by auto
  from vs2 asne have "hd vs = hd as" by simp
  with yh have "y = hd as" by auto
  with asne have "y \<in> set as" by (induct as) auto
  with d xbs vs2 show False by auto
qed

lemma is_sublist_at1: "distinct (as @ bs) \<Longrightarrow> is_sublist [x,y] (as @ bs) \<Longrightarrow> x \<noteq> (last as)  \<Longrightarrow>
  is_sublist [x,y] as \<or> is_sublist [x,y] bs"
proof (cases "x \<in> set as")
  assume d: "distinct (as @ bs)"  and subl: "is_sublist [x, y] (as @ bs)" and xnl: "x \<noteq> last as"
  define vs where "vs = as @ bs"
  with d have dvs: "distinct vs" by auto
  case True
  with xnl subl have ind: "is_sublist (as@bs) vs \<Longrightarrow> is_sublist [x, y] as"
  proof (induct as)
    case Nil
    then show ?case by force
  next
    case (Cons a as)
    assume ih: "\<lbrakk>is_sublist (as@bs) vs; x \<noteq> last as; is_sublist [x,y] (as @ bs); x \<in> set as\<rbrakk> \<Longrightarrow>
      is_sublist [x, y] as" and subl_aas_vs: "is_sublist ((a # as) @ bs) vs"
      and xnl2: "x \<noteq> last (a # as)" and subl2: "is_sublist [x, y] ((a # as) @ bs)"
      and x: "x \<in> set (a # as)"
    then have rule1: "x \<noteq> a \<Longrightarrow> is_sublist [x,y] as" apply (cases "as = []") apply simp
      apply (rule_tac ih) by (auto dest: is_sublist_tl)

    from dvs subl_aas_vs have daas: "distinct (a # as @ bs)" apply (rule_tac is_sublist_distinct) by auto
    from xnl2 have asne: "x = a \<Longrightarrow> as \<noteq> []" by auto
    with subl2 daas have yhdas: "x = a \<Longrightarrow> y = hd as" apply simp apply (drule_tac is_sublist_distinct_prefix) by auto
    with asne have "x = a \<Longrightarrow> as = y # tl as" by auto
    with asne yhdas have "x = a \<Longrightarrow> is_prefix [x,y] (a # as)" by auto
    then have rule2: "x = a \<Longrightarrow> is_sublist [x,y] (a # as)" by (simp add: is_prefix_sublist)

    from rule1 rule2 show ?case by (cases "x = a") auto
  qed
  from vs_def d have "is_sublist [x, y] as" by (rule_tac ind) auto
  then show ?thesis by auto
next
  assume d: "distinct (as @ bs)"  and subl: "is_sublist [x, y] (as @ bs)" and xnl: "x \<noteq> last as"
  define ars where "ars = as"
  case False
  with ars_def have xars: "x \<notin> set ars" by auto
  from subl have ind: "is_sublist as ars \<Longrightarrow> is_sublist [x, y] bs"
  proof (induct as)
    case Nil
    then show ?case by auto
  next
    case (Cons a as)
    assume ih: "\<lbrakk>is_sublist as ars; is_sublist [x, y] (as @ bs)\<rbrakk> \<Longrightarrow> is_sublist [x, y] bs"
      and subl_aasbsvs: "is_sublist (a # as) ars" and subl2: "is_sublist [x, y] ((a # as) @ bs)"
    from subl_aasbsvs ars_def False have "x \<noteq> a" by (auto simp:is_sublist_in)
    with subl_aasbsvs subl2 show ?thesis apply (rule_tac ih) by (auto dest: is_sublist_tl)
  qed
  from ars_def have "is_sublist [x, y] bs" by (rule_tac ind) auto
  then show ?thesis by auto
qed

lemma is_sublist_at4: "distinct (as @ bs) \<Longrightarrow> is_sublist [x,y] (as @ bs) \<Longrightarrow>
  as \<noteq> [] \<Longrightarrow> x = last as \<Longrightarrow> y = hd bs"
proof -
  assume d: "distinct (as @ bs)" and subl: "is_sublist [x,y] (as @ bs)"
    and asne: "as \<noteq> []" and xl: "x = last as"
  define vs where "vs = as @ bs"
  with subl have "is_sublist [x,y] vs" by auto
  then obtain rs ts where vs2: "vs = rs @ x # y # ts" by (auto simp: is_sublist_def)
  from vs_def d have dvs:"distinct vs" by auto
  from asne xl have as:"as = butlast as @ [x]" by auto
  with vs_def have vs3: "vs = butlast as @ x # bs" by auto
  from dvs vs2 vs3 have "rs = butlast as" apply (rule_tac dist_at1) by auto
  then have "rs @ [x] = butlast as @ [x]" by auto
  with as have "rs @ [x] = as" by auto
  then have "as = rs @ [x]" by auto
  with vs2 vs_def have "bs = y # ts" by auto
  then show ?thesis by auto
qed

lemma is_sublist_at5: "distinct (as @ bs) \<Longrightarrow> is_sublist [x,y] (as @ bs) \<Longrightarrow>
  is_sublist [x,y] as \<or> is_sublist [x,y] bs \<or> x = last as \<and> y = hd bs"
  apply (case_tac "as = []") apply simp apply (cases "x = last as")
  apply (subgoal_tac "y = hd bs") apply simp
  apply (rule is_sublist_at4) apply assumption+  (*apply force+ *)
  apply (drule_tac is_sublist_at1) by auto

lemma is_sublist_rev: "is_sublist [a,b] (rev zs) = is_sublist [b,a] zs"
  apply (simp add: is_sublist_def)
    apply (intro iffI) apply (elim exE) apply (intro exI)
    apply (subgoal_tac "zs = (rev bs) @ b # a # rev as") apply assumption
    apply (subgoal_tac "rev (rev zs) = rev (as @ a # b # bs)")
      apply (thin_tac "rev zs = as @ a # b # bs") apply simp
      apply simp
    apply (elim exE) apply (intro exI) by force

lemma is_sublist_at5'[simp]:
 "distinct as \<Longrightarrow> distinct bs \<Longrightarrow> set as \<inter> set bs = {} \<Longrightarrow> is_sublist [x,y] (as @ bs) \<Longrightarrow>
 is_sublist [x,y] as \<or> is_sublist [x,y] bs \<or> x = last as \<and> y = hd bs"
apply (subgoal_tac "distinct (as @ bs)") apply (drule is_sublist_at5) by auto

lemma splitAt_is_sublist1R[simp]: "ram \<in> set vs \<Longrightarrow> is_sublist (fst (splitAt ram vs) @ [ram]) vs"
apply (auto dest!: splitAt_ram simp: is_sublist_def) apply (intro exI)
apply (subgoal_tac "vs = [] @ fst (splitAt ram vs) @ ram # snd (splitAt ram vs)") apply assumption by simp

lemma splitAt_is_sublist2R[simp]: "ram \<in> set vs \<Longrightarrow> is_sublist (ram # snd (splitAt ram vs)) vs"
apply (auto dest!: splitAt_ram splitAt_no_ram simp: is_sublist_def) apply (intro exI)
apply (subgoal_tac "vs = fst (splitAt ram vs) @ ram # snd (splitAt ram vs) @ []") apply assumption by auto



(*********************** section is_nextElem *****************************)
subsection \<open>\<open>is_nextElem\<close>\<close>

definition is_nextElem :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
 "is_nextElem xs x y \<equiv> is_sublist [x,y] xs \<or> xs \<noteq> [] \<and> x = last xs \<and> y = hd xs"

lemma is_nextElem_a[intro]: "is_nextElem vs a b \<Longrightarrow> a \<in> set vs"
  by (auto simp: is_nextElem_def is_sublist_def)
lemma is_nextElem_b[intro]: "is_nextElem vs a b \<Longrightarrow> b \<in> set vs"
  by (auto simp: is_nextElem_def is_sublist_def)
lemma is_nextElem_last_hd[intro]: "distinct vs \<Longrightarrow> is_nextElem vs x y \<Longrightarrow>
  x = last vs \<Longrightarrow> y = hd vs"
  by (auto simp: is_nextElem_def)
lemma is_nextElem_last_ne[intro]: "distinct vs \<Longrightarrow> is_nextElem vs x y \<Longrightarrow>
  x = last vs \<Longrightarrow> vs \<noteq> []"
  by (auto simp: is_nextElem_def)
lemma is_nextElem_sublistI: "is_sublist [x,y] vs \<Longrightarrow> is_nextElem vs x y"
  by (auto simp: is_nextElem_def)

lemma is_nextElem_nth1: "is_nextElem ls x y \<Longrightarrow> \<exists> i j. i < length ls
  \<and> j < length ls \<and> ls!i = x \<and> ls!j = y \<and> (Suc i) mod (length ls) = j"
proof (cases "is_sublist [x,y] ls")
  assume is_nextElem: "is_nextElem ls x y"
  case True then show ?thesis apply (drule_tac is_sublist_nth1) by auto
next
  assume is_nextElem: "is_nextElem ls x y"
  case False with is_nextElem have hl: "ls \<noteq> [] \<and> last ls = x \<and> hd ls = y"
    by (auto simp: is_nextElem_def)
  then have j: "ls!0 = y" by (cases ls) auto
  from hl have i: "ls!(length ls - 1) = x" by (cases ls rule: rev_exhaust)  auto
  from i j hl have "(length ls - 1) < length ls \<and> 0 < length ls \<and> ls!(length ls - 1) = x
    \<and> ls!0 = y \<and> (Suc (length ls - 1)) mod (length ls) = 0" by auto
  then show ?thesis apply (intro exI) .
qed

lemma is_nextElem_nth2: " \<exists> i j. i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y
   \<and> (Suc i) mod (length ls) = j \<Longrightarrow> is_nextElem ls x y"
proof -
  assume "\<exists> i j. i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y \<and> (Suc i) mod (length ls) = j"
  then obtain i j where vors: "i < length ls \<and> j < length ls \<and> ls!i = x \<and> ls!j = y
    \<and> (Suc i) mod (length ls) = j" by auto
  then show ?thesis
  proof (cases "Suc i = length ls")
    case True with vors have "j = 0" by auto
      (*ls ! i = last ls*)
    with True vors show ?thesis apply (auto simp: is_nextElem_def)
     apply (cases ls rule: rev_exhaust) apply auto apply (cases ls) by auto
  next
    case False with vors have "is_sublist [x,y] ls"
    apply (rule_tac is_sublist_nth2) by auto
    then show ?thesis by (simp add: is_nextElem_def)
  qed
qed

lemma is_nextElem_rotate1_aux:
  "is_nextElem (rotate m ls) x y \<Longrightarrow> is_nextElem ls x y"
proof -
  assume is_nextElem: "is_nextElem (rotate m ls) x y"
  define n where "n = m mod length ls"
  then have rot_eq: "rotate m ls = rotate n ls"
    by (auto intro: rotate_conv_mod)
  with is_nextElem have "is_nextElem (rotate n ls) x y"
    by simp
  then obtain i j where vors:"i < length (rotate n ls) \<and> j < length (rotate n ls) \<and>
    (rotate n ls)!i = x \<and> (rotate n ls)!j = y \<and>
    (Suc i) mod (length (rotate n ls)) = j"
    by (drule_tac is_nextElem_nth1) auto
  then have lls: "0 < length ls"
    by auto
  define k where "k = (i+n) mod (length ls)"
  with lls have sk: "k < length ls"
    by simp
  from k_def lls vors have "ls!k = (rotate n ls)!(i mod (length ls))"
    by (simp add: nth_rotate)
  with vors have lsk: "ls!k = x"
    by simp
  define l where "l = (j+n) mod (length ls)"
  with lls have sl: "l < length ls"
    by simp
  from l_def lls vors have "ls!l = (rotate n ls)!(j mod (length ls))"
    by (simp add: nth_rotate)
  with vors have lsl: "ls!l = y"
    by simp
  from vors k_def l_def
  have "(Suc i) mod length ls = j"
    by simp
  then have "(Suc i) mod length ls = j mod length ls"
    by auto
  then have "((Suc i) mod length ls + n mod (length ls)) mod length ls
    = (j mod length ls + n mod (length ls)) mod length ls"
    by simp
  then have "((Suc i) + n) mod length ls = (j + n) mod length ls"
    by (simp add: mod_simps)
  with vors k_def l_def have "(Suc k) mod (length ls) = l"
    by (simp add: mod_simps)
  with sk lsk sl lsl
  show ?thesis
    by (auto intro: is_nextElem_nth2)
qed

lemma is_nextElem_rotate_eq[simp]: "is_nextElem (rotate m ls) x y = is_nextElem ls x y"
  apply (auto dest: is_nextElem_rotate1_aux) apply (rule is_nextElem_rotate1_aux)
  apply (subgoal_tac   "is_nextElem (rotate (length ls - m mod length ls) (rotate m ls)) x y")
  apply assumption by simp

lemma is_nextElem_congs_eq: "ls \<cong> ms \<Longrightarrow> is_nextElem ls x y = is_nextElem ms x y"
by (auto simp: congs_def)

lemma is_nextElem_rev[simp]: "is_nextElem (rev zs) a b = is_nextElem zs b a"
  apply (simp add: is_nextElem_def is_sublist_rev)
  apply (case_tac "zs = []") apply simp apply simp
  apply (case_tac "a = hd zs") apply (case_tac "zs")  apply simp  apply simp apply simp
  apply (case_tac "a = last (rev zs) \<and> b = last zs") apply simp
    apply (case_tac "zs" rule: rev_exhaust) apply simp
    apply (case_tac "ys") apply simp apply simp by force


lemma is_nextElem_circ:
  "\<lbrakk> distinct xs; is_nextElem xs a b; is_nextElem xs b a \<rbrakk> \<Longrightarrow> |xs| \<le> 2"
apply(drule is_nextElem_nth1)
apply(drule is_nextElem_nth1)
apply (clarsimp)
apply(rename_tac i j)
apply(frule_tac i=j and j = "Suc i mod |xs|" in nth_eq_iff_index_eq)
  apply assumption+
apply(frule_tac j=i and i = "Suc j mod |xs|" in nth_eq_iff_index_eq)
  apply assumption+
apply(rule ccontr)
apply(simp add: distinct_conv_nth mod_Suc)
done


subsection\<open>\<open>nextElem, sublist, is_nextElem\<close>\<close>

lemma is_sublist_eq: "distinct vs \<Longrightarrow> c \<noteq> y \<Longrightarrow>
 (nextElem vs c x = y) = is_sublist [x,y] vs"
proof -
  assume d: "distinct vs" and c: "c \<noteq> y"
  have r1: "nextElem vs c x = y \<Longrightarrow> is_sublist [x,y] vs"
  proof -
    assume fn: "nextElem vs c x = y"
    with c show ?thesis by(drule_tac nextElem_cases)(auto simp: is_sublist_def)
  qed
  with d have r2: "is_sublist [x,y] vs \<Longrightarrow> nextElem vs c x = y"
  apply (simp add: is_sublist_def) apply (elim exE) by auto
  show ?thesis apply (intro iffI r1) by (auto intro: r2)
qed

lemma is_nextElem1: "distinct vs \<Longrightarrow> x \<in> set vs \<Longrightarrow> nextElem vs (hd vs) x = y \<Longrightarrow> is_nextElem vs x y"
proof -
  assume d: "distinct vs" and x: "x \<in> set vs" and fn: "nextElem vs (hd vs) x = y"
  from x have r0: "vs \<noteq> []" by auto
  from d fn have r1: "x = last vs \<Longrightarrow> y = hd vs" by (auto)
  from d fn have r3: "hd vs \<noteq> y \<Longrightarrow> (\<exists> a b. vs = a @ [x,y] @ b)" by (drule_tac nextElem_cases) auto

  from x obtain n where xn:"x = vs!n" and nl: "n < length vs" by (auto simp: in_set_conv_nth)
  define as where "as = take n vs"
  define bs where "bs = drop (Suc n) vs"
  from as_def bs_def xn nl have vs:"vs = as @ [x] @ bs" by (auto intro: id_take_nth_drop)
  then have r2: "x \<noteq> last vs \<Longrightarrow> y \<noteq> hd vs"
  proof -
    assume notx: "x \<noteq> last vs"
    from vs notx have "bs \<noteq> []" by auto
    with vs have r2: "vs = as @ [x, hd bs] @ tl bs" by auto
    with d have ineq: "hd bs \<noteq> hd vs" by (cases as) auto
    from d fn r2 have "y = hd bs" by auto
    with ineq show ?thesis by auto
  qed
  from r0 r1 r2 r3 show ?thesis apply (simp add:is_nextElem_def is_sublist_def)
   apply (cases "x = last vs") by auto
qed

lemma is_nextElem2: "distinct vs \<Longrightarrow> x \<in> set vs \<Longrightarrow> is_nextElem vs x y \<Longrightarrow> nextElem vs (hd vs) x = y"
proof -
  assume d: "distinct vs" and x: "x \<in> set vs" and is_nextElem: "is_nextElem vs x y"
  then show ?thesis apply (simp add: is_nextElem_def) apply (cases "is_sublist [x,y] vs")
    apply (cases "y = hd vs")
    apply (simp add: is_sublist_def) apply (force dest: distinct_hd_not_cons)
    apply (subgoal_tac "hd vs \<noteq> y")  apply (simp add: is_sublist_eq) by auto
qed

lemma nextElem_is_nextElem:
 "distinct xs \<Longrightarrow> x \<in> set xs \<Longrightarrow>
   is_nextElem xs x y = (nextElem xs (hd xs) x = y)"
  by (auto intro!: is_nextElem1 is_nextElem2)

lemma nextElem_congs_eq: "xs \<cong> ys \<Longrightarrow> distinct xs \<Longrightarrow> x \<in> set xs  \<Longrightarrow>
   nextElem xs (hd xs) x = nextElem ys (hd ys) x"
proof -
  assume eq: "xs \<cong> ys" and dist: "distinct xs" and x: "x \<in> set xs"
  define y where "y = nextElem xs (hd xs) x"
  then have f1:"nextElem xs (hd xs) x = y" by auto
  with dist x have "is_nextElem xs x y" by (auto intro: is_nextElem1)
  with eq have "is_nextElem ys x y" by (simp add:is_nextElem_congs_eq)
  with eq dist x have f2:"nextElem ys (hd ys) x = y"
    by (auto simp: congs_distinct intro: is_nextElem2)
  from f1 f2 show ?thesis by auto
qed


lemma is_sublist_is_nextElem: "distinct vs \<Longrightarrow> is_nextElem vs x y \<Longrightarrow> is_sublist as vs \<Longrightarrow> x \<in> set as \<Longrightarrow> x \<noteq> last as \<Longrightarrow> is_sublist [x,y] as"
proof -
  assume d: "distinct vs" and is_nextElem: "is_nextElem vs x y" and subl: "is_sublist as vs" and xin: "x \<in> set as" and xnl: "x \<noteq> last as"
  from xin have asne: "as \<noteq> []" by auto
  with subl have vsne: "vs \<noteq> []" by (auto simp: is_sublist_def)
  from subl obtain rs ts where vs: "vs = rs @ as @ ts"  apply (simp add: is_sublist_def) apply (elim exE) by auto
  with d xnl asne have "x \<noteq> last vs"
  proof (cases "ts = []")
    case True
    with d xnl asne vs show ?thesis by force
  next
    define lastvs where "lastvs = last ts"
    case False
    with vs lastvs_def have vs2: "vs = rs @ as @ butlast ts @ [lastvs]" by auto
    with d have "lastvs \<notin> set as" by auto
    with xin have "lastvs \<noteq> x" by auto
    with vs2 show ?thesis by auto
  qed
  with is_nextElem have subl_vs: "is_sublist [x,y] vs" by (auto simp: is_nextElem_def)
  from d xin vs have "\<not> is_sublist [x] rs" by auto
  then have nrs: "\<not> is_sublist [x,y] rs" by (auto dest: is_sublist_hd)
  from d xin vs have "\<not> is_sublist [x] ts" by auto
  then have nts: "\<not> is_sublist [x,y] ts" by (auto dest: is_sublist_hd)
  from d xin vs have xnrs: "x \<notin> set rs" by auto
  then have notrs: "\<not> is_sublist [x,y] rs" by (auto simp:is_sublist_in)
  from xnrs have xnlrs: "rs \<noteq> [] \<Longrightarrow> x \<noteq> last rs" by (induct rs) auto
  from d xin vs have xnts: "x \<notin> set ts" by auto
  then have notts: "\<not> is_sublist [x,y] ts"  by (auto simp:is_sublist_in)
  from d vs subl_vs have "is_sublist [x,y] rs \<or> is_sublist [x,y] (as@ts)" apply (cases "rs = []") apply simp apply (rule_tac is_sublist_at1) by (auto intro!: xnlrs)
  with notrs have "is_sublist [x,y] (as@ts)" by auto
  with d vs xnl have "is_sublist [x,y] as \<or> is_sublist [x,y] ts" apply (rule_tac is_sublist_at1) by auto
  with notts show "is_sublist [x,y] as"  by auto
qed


subsection \<open>\<open>before\<close>\<close>

definition before :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"before vs ram1 ram2 \<equiv> \<exists> a b c. vs = a @ ram1 # b @ ram2 # c"

lemma before_dist_fst_fst[simp]: "before vs ram1 ram2 \<Longrightarrow> distinct vs \<Longrightarrow> fst (splitAt ram2 (fst (splitAt ram1 vs))) = fst (splitAt ram1 (fst (splitAt ram2 vs)))"
  apply (simp add: before_def) apply (elim exE)
  apply (drule splitAt_dist_ram_all) by (auto dest!: pairD)

lemma before_dist_fst_snd[simp]: "before vs ram1 ram2 \<Longrightarrow> distinct vs \<Longrightarrow> fst (splitAt ram2 (snd (splitAt ram1 vs))) = snd (splitAt ram1 (fst (splitAt ram2 vs)))"
  apply (simp add: before_def) apply (elim exE)
  apply (drule_tac splitAt_dist_ram_all) by (auto dest!: pairD)

lemma before_dist_snd_fst[simp]: "before vs ram1 ram2 \<Longrightarrow> distinct vs \<Longrightarrow> snd (splitAt ram2 (fst (splitAt ram1 vs))) = snd (splitAt ram1 (snd (splitAt ram2 vs)))"
  apply (simp add: before_def) apply (elim exE)
  apply (drule_tac splitAt_dist_ram_all) by (auto dest!: pairD)

lemma before_dist_snd_snd[simp]: "before vs ram1 ram2 \<Longrightarrow> distinct vs \<Longrightarrow> snd (splitAt ram2 (snd (splitAt ram1 vs))) = fst (splitAt ram1 (snd (splitAt ram2 vs)))"
  apply (simp add: before_def) apply (elim exE)
  apply (drule_tac splitAt_dist_ram_all) by (auto dest!: pairD)

lemma before_dist_snd[simp]: "before vs ram1 ram2 \<Longrightarrow> distinct vs \<Longrightarrow> fst (splitAt ram1 (snd (splitAt ram2 vs))) = snd (splitAt ram2 vs)"
  apply (simp add: before_def) apply (elim exE)
  apply (drule_tac splitAt_dist_ram_all)   by (auto dest!: pairD)

lemma before_dist_fst[simp]: "before vs ram1 ram2 \<Longrightarrow> distinct vs \<Longrightarrow> fst (splitAt ram1 (fst (splitAt ram2 vs))) = fst (splitAt ram1 vs)"
  apply (simp add: before_def) apply (elim exE)
  apply (drule_tac splitAt_dist_ram_all)   by (auto dest!: pairD)

lemma before_or: "ram1 \<in> set vs \<Longrightarrow> ram2 \<in> set vs \<Longrightarrow> ram1 \<noteq> ram2 \<Longrightarrow> before vs ram1 ram2 \<or> before vs ram2 ram1"
proof -
  assume r1: "ram1 \<in> set vs" and r2: "ram2 \<in> set vs" and r12: "ram1 \<noteq> ram2"
  then show ?thesis
    proof (cases "ram2 \<in> set (snd (splitAt ram1 vs))")
      define a where "a = fst (splitAt ram1 vs)"
      define b where "b = fst (splitAt ram2 (snd (splitAt ram1 vs)))"
      define c where "c = snd (splitAt ram2 (snd (splitAt ram1 vs)))"
      case True with r1 a_def b_def c_def have "vs = a @ [ram1] @ b @ [ram2] @ c"
        by (auto dest!: splitAt_ram)
      then show ?thesis apply (simp add: before_def) by auto
    next
      define ab where "ab = fst (splitAt ram1 vs)"
      case False
      with r1 r2 r12 ab_def have r2': "ram2 \<in> set ab" by (auto intro: splitAt_ram3)
      define a where "a = fst (splitAt ram2 ab)"
      define b where "b = snd (splitAt ram2 ab)"
      define c where "c = snd (splitAt ram1 vs)"
      from r1 ab_def c_def have "vs = ab @ [ram1] @ c" by (auto dest!: splitAt_ram)
      with r2' a_def b_def have "vs = (a @ [ram2] @ b) @ [ram1] @ c" by (drule_tac splitAt_ram) simp
      then show ?thesis apply (simp add: before_def) apply (rule disjI2) by auto
    qed
  qed

lemma before_r1:
  "before vs r1 r2 \<Longrightarrow> r1 \<in> set vs" by (auto simp: before_def)

lemma before_r2:
  "before vs r1 r2 \<Longrightarrow> r2 \<in> set vs" by (auto simp: before_def)

lemma before_dist_r2:
  "distinct vs \<Longrightarrow> before vs r1 r2 \<Longrightarrow> r2 \<in> set (snd (splitAt r1 vs))"
proof -
  assume d: "distinct vs" and b: "before vs r1 r2"
  from d b have ex1: "\<exists>! s. (vs = (fst s) @ r1 # snd (s))" apply (drule_tac before_r1) apply (rule distinct_unique1)  by auto
  from d b ex1 show ?thesis apply (unfold before_def)
    proof (elim exE ex1E)
      fix a b c s
      assume vs: "vs = a @ r1 # b @ r2 # c" and "\<forall>y. vs = fst y @ r1 # snd y \<longrightarrow> y = s"
      then have  "\<And> y. vs = fst y @ r1 # snd y \<longrightarrow> y = s" by (clarify, hypsubst_thin, auto)
      then have single: "\<And> y. vs = fst y @ r1 # snd y \<Longrightarrow> y = s" by auto
      define bc where "bc = b @ r2 # c"
      with vs have vs2: "vs = a @ r1 # bc" by auto
      from bc_def have  r2: "r2 \<in> set bc" by auto
      define t where "t = (a,bc)"
      with vs2 have vs3: "vs = fst (t) @ r1 # snd (t)" by auto
      with single have ts: "t = s" by (rule_tac single) auto
      from b have "splitAt r1 vs = s" apply (drule_tac before_r1) apply (drule_tac splitAt_ram) by (rule single) auto
      with ts have "t = splitAt r1 vs" by simp
      with t_def have "bc = snd(splitAt r1 vs)" by simp
      with r2 show ?thesis by simp
    qed
  qed

lemma before_dist_not_r2[intro]:
  "distinct vs \<Longrightarrow> before vs r1 r2 \<Longrightarrow> r2 \<notin>  set (fst (splitAt r1 vs))" apply (frule before_dist_r2) by (auto dest: splitAt_distinct_fst_snd)

lemma before_dist_r1:
  "distinct vs \<Longrightarrow> before vs r1 r2 \<Longrightarrow> r1 \<in> set (fst (splitAt r2 vs))"
proof -
  assume d: "distinct vs" and b: "before vs r1 r2"
  from d b have ex1: "\<exists>! s. (vs = (fst s) @ r2 # snd (s))" apply (drule_tac before_r2) apply (rule distinct_unique1)  by auto
  from d b ex1 show ?thesis apply (unfold before_def)
    proof (elim exE ex1E)
      fix a b c s
      assume vs: "vs = a @ r1 # b @ r2 # c" and "\<forall>y. vs = fst y @ r2 # snd y \<longrightarrow> y = s"
      then have  "\<And> y. vs = fst y @ r2 # snd y \<longrightarrow> y = s" by (clarify, hypsubst_thin, auto)
      then have single: "\<And> y. vs = fst y @ r2 # snd y \<Longrightarrow> y = s" by auto
      define ab where "ab = a @ r1 # b"
      with vs have vs2: "vs = ab @ r2 # c" by auto
      from ab_def have  r1: "r1 \<in> set ab" by auto
      define t where "t = (ab,c)"
      with vs2 have vs3: "vs = fst (t) @ r2 # snd (t)" by auto
      with single have ts: "t = s" by (rule_tac single) auto
      from b have "splitAt r2 vs = s" apply (drule_tac before_r2) apply (drule_tac splitAt_ram) by (rule single) auto
      with ts have "t = splitAt r2 vs" by simp
      with t_def have "ab = fst(splitAt r2 vs)" by simp
      with r1 show ?thesis by simp
    qed
  qed

lemma before_dist_not_r1[intro]:
  "distinct vs \<Longrightarrow> before vs r1 r2 \<Longrightarrow> r1 \<notin>  set (snd (splitAt r2 vs))" apply (frule before_dist_r1) by (auto dest: splitAt_distinct_fst_snd)

lemma before_snd:
  "r2 \<in> set (snd (splitAt r1 vs)) \<Longrightarrow> before vs r1 r2"
proof -
  assume r2: "r2 \<in> set (snd (splitAt r1 vs))"
  from r2 have r1: "r1 \<in> set vs" apply (rule_tac ccontr) apply (drule splitAt_no_ram) by simp
  define a where "a = fst (splitAt r1 vs)"
  define bc where "bc = snd (splitAt r1 vs)"
  define b where "b = fst (splitAt r2 bc)"
  define c where "c = snd (splitAt r2 bc)"
  from r1 a_def bc_def have vs: "vs = a @ [r1] @ bc" by (auto dest: splitAt_ram)
  from r2 bc_def have r2: "r2 \<in> set bc" by simp
  with b_def c_def have "bc = b @ [r2] @ c" by (auto dest: splitAt_ram)
  with vs show ?thesis by (simp add: before_def) auto
qed

lemma before_fst:
"r2 \<in> set vs \<Longrightarrow> r1 \<in> set (fst (splitAt r2 vs)) \<Longrightarrow> before vs r1 r2"
proof -
  assume r2: "r2 \<in> set vs" and r1: "r1 \<in> set (fst (splitAt r2 vs))"
  define ab where "ab = fst (splitAt r2 vs)"
  define c where "c = snd (splitAt r2 vs)"
  define a where "a = fst (splitAt r1 ab)"
  define b where "b = snd (splitAt r1 ab)"
  from r2 ab_def c_def have vs: "vs = ab @ [r2] @ c" by (auto dest: splitAt_ram)
  from r1 ab_def have r1: "r1 \<in> set ab" by simp
  with a_def b_def have "ab = a @ [r1] @ b" by (auto dest: splitAt_ram)
  with vs show ?thesis by (simp add: before_def) auto
qed

(* usefule simplifier rules *)
lemma before_dist_eq_fst:
"distinct vs \<Longrightarrow> r2 \<in> set vs \<Longrightarrow> r1 \<in> set (fst (splitAt r2 vs)) = before vs r1 r2"
  by (auto intro: before_fst before_dist_r1)

lemma before_dist_eq_snd:
"distinct vs \<Longrightarrow> r2 \<in> set (snd (splitAt r1 vs)) = before vs r1 r2"
  by (auto intro: before_snd before_dist_r2)

lemma before_dist_not1:
  "distinct vs \<Longrightarrow> before vs ram1 ram2 \<Longrightarrow> \<not> before vs ram2 ram1"
proof
   assume d: "distinct vs" and b1: "before vs ram2 ram1" and b2: "before vs ram1 ram2"
   from b2 have r1: "ram1 \<in> set vs" by (drule_tac before_r1)
   from d b1 have r2: "ram2 \<in> set (fst (splitAt ram1 vs))" by (rule before_dist_r1)
   from d b2 have r2':"ram2 \<in> set (snd (splitAt ram1 vs))" by (rule before_dist_r2)
   from d r1 r2 r2' show "False" by (drule_tac splitAt_distinct_fst_snd) auto
qed

lemma before_dist_not2:
  "distinct vs \<Longrightarrow> ram1 \<in> set vs \<Longrightarrow> ram2 \<in> set vs \<Longrightarrow> ram1 \<noteq> ram2 \<Longrightarrow> \<not> (before vs ram1 ram2) \<Longrightarrow> before vs ram2 ram1"
proof -
  assume "distinct vs" "ram1 \<in> set vs " "ram2 \<in> set vs" "ram1 \<noteq> ram2" "\<not> before vs ram1 ram2"
  then show "before vs ram2 ram1" apply (frule_tac before_or) by auto
qed

lemma before_dist_eq:
  "distinct vs \<Longrightarrow> ram1 \<in> set vs \<Longrightarrow> ram2 \<in> set vs \<Longrightarrow> ram1 \<noteq> ram2 \<Longrightarrow> ( \<not> (before vs ram1 ram2)) = before vs ram2 ram1"
  by (auto intro: before_dist_not2 dest: before_dist_not1)

lemma before_vs:
 "distinct vs \<Longrightarrow> before vs ram1 ram2 \<Longrightarrow> vs = fst (splitAt ram1 vs) @ ram1 # fst (splitAt ram2 (snd (splitAt ram1 vs))) @ ram2 # snd (splitAt ram2 vs)"
proof -
  assume d: "distinct vs" and b: "before vs ram1 ram2"
  define s where "s = snd (splitAt ram1 vs)"
  from b have  "ram1 \<in> set vs" by (auto simp: before_def)
  with s_def have vs: "vs = fst (splitAt ram1 vs) @ [ram1] @ s" by (auto dest: splitAt_ram)
  from d b s_def have "ram2 \<in> set s" by (auto intro: before_dist_r2)
  then have snd: "s = fst (splitAt ram2 s) @ [ram2] @  snd (splitAt ram2 s)"
    by (auto dest: splitAt_ram)
  with vs have "vs = fst (splitAt ram1 vs) @ [ram1] @ fst (splitAt ram2 s) @ [ram2] @  snd (splitAt ram2 s)" by auto
  with d b s_def show ?thesis by auto
qed




(************************ between lemmas *************************************)
subsection \<open>@{const between}\<close>

definition pre_between :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"pre_between vs ram1 ram2 \<equiv>
   distinct vs \<and> ram1 \<in> set vs \<and> ram2 \<in> set vs \<and> ram1 \<noteq> ram2"

declare pre_between_def [simp]

lemma pre_between_dist[intro]:
  "pre_between vs ram1 ram2 \<Longrightarrow> distinct vs" by (auto simp: pre_between_def)

lemma pre_between_r1[intro]:
  "pre_between vs ram1 ram2 \<Longrightarrow> ram1 \<in> set vs" by auto

lemma pre_between_r2[intro]:
  "pre_between vs ram1 ram2 \<Longrightarrow> ram2 \<in> set vs" by auto

lemma pre_between_r12[intro]:
  "pre_between vs ram1 ram2 \<Longrightarrow> ram1 \<noteq> ram2" by auto

lemma pre_between_symI:
  "pre_between vs ram1 ram2 \<Longrightarrow> pre_between vs ram2 ram1" by auto

lemma pre_between_before[dest]:
  "pre_between vs ram1 ram2 \<Longrightarrow> before vs ram1 ram2 \<or> before vs ram2 ram1" by (rule_tac before_or) auto

lemma pre_between_rotate1[intro]:
  "pre_between vs ram1 ram2 \<Longrightarrow> pre_between (rotate1 vs) ram1 ram2" by auto

lemma pre_between_rotate[intro]:
  "pre_between vs ram1 ram2 \<Longrightarrow> pre_between (rotate n vs) ram1 ram2" by auto

lemma(*<*) before_xor: (*>*)
 "pre_between vs ram1 ram2 \<Longrightarrow> (\<not> before vs ram1 ram2) = before vs ram2 ram1"
  by (simp add: before_dist_eq)

declare pre_between_def [simp del]

lemma between_simp1[simp]:
"before vs ram1 ram2 \<Longrightarrow> pre_between vs ram1 ram2 \<Longrightarrow>
between vs ram1 ram2 = fst (splitAt ram2 (snd (splitAt ram1 vs)))"
by (simp add: pre_between_def between_def split_def before_dist_eq_snd)


lemma between_simp2[simp]:
"before vs ram1 ram2 \<Longrightarrow> pre_between vs ram1 ram2 \<Longrightarrow>
  between vs ram2 ram1 = snd (splitAt ram2 vs) @  fst (splitAt ram1 vs)"
proof -
  assume b: "before vs ram1 ram2" and p: "pre_between vs ram1 ram2"
  from p b have b2: "\<not> before vs ram2 ram1" apply (simp add: pre_between_def) by (auto dest: before_dist_not1)
  with p have "ram2 \<notin> set (fst (splitAt ram1 vs))" by (simp add: pre_between_def before_dist_eq_fst)
  then have "fst (splitAt ram1 vs) = fst (splitAt ram2 (fst (splitAt ram1 vs)))" by (auto dest: splitAt_no_ram)
  then have "fst (splitAt ram2 (fst (splitAt ram1 vs))) = fst (splitAt ram1 vs)" by auto
  with b2 b p show ?thesis apply (simp add: pre_between_def between_def split_def)
    by (auto dest: before_dist_not_r1)
qed

lemma between_not_r1[intro]:
  "distinct vs \<Longrightarrow> ram1 \<notin> set (between vs ram1 ram2)"
proof (cases "pre_between vs ram1 ram2")
  assume d: "distinct vs"
  case True then have p: "pre_between vs ram1 ram2" by auto
  then show "ram1 \<notin> set (between vs ram1 ram2)"
  proof (cases "before vs ram1 ram2")
    case True with d p show ?thesis by (auto del: notI)
  next
    from p have p2: "pre_between vs ram2 ram1" by (auto intro: pre_between_symI)
    case False with p have "before vs ram2 ram1" by auto
    with d p2 show ?thesis  by (auto del: notI)
  qed
next
  assume d:"distinct vs"
  case False then have p: "\<not> pre_between vs ram1 ram2" by auto
  then show ?thesis
  proof (cases "ram1 = ram2")
    case True with d have h1:"ram2 \<notin> set (snd (splitAt ram2 vs))" by (auto del: notI)
    from True d have h2: "ram2 \<notin> set (fst (splitAt ram2 (fst (splitAt ram2 vs))))" by (auto del: notI)
    with True d h1 show ?thesis by (auto simp: between_def split_def)
  next
    case False then have neq: "ram1 \<noteq> ram2" by auto
    then show ?thesis
    proof (cases "ram1 \<notin> set vs")
      case True with d show ?thesis by (auto dest: splitAt_no_ram splitAt_in_fst simp: between_def split_def)
    next
      case False then have r1in: "ram1 \<in> set vs" by auto
      then show ?thesis
      proof (cases "ram2 \<notin> set vs")
        from d have h1: "ram1 \<notin> set (fst (splitAt ram1 vs))" by (auto del: notI)
        case True with d h1 show ?thesis
        by (auto dest: splitAt_not1 splitAt_in_fst splitAt_ram
        splitAt_no_ram simp: between_def split_def del: notI)
      next
        case False then have r2in: "ram2 \<in> set vs" by auto
        with d neq r1in have "pre_between vs ram1 ram2"
          by (auto simp: pre_between_def)
        with p show ?thesis by auto
      qed
    qed
  qed
qed

lemma between_not_r2[intro]:
  "distinct vs \<Longrightarrow> ram2 \<notin> set (between vs ram1 ram2)"
proof (cases "pre_between vs ram1 ram2")
  assume d: "distinct vs"
  case True then have p: "pre_between vs ram1 ram2" by auto
  then show "ram2 \<notin> set (between vs ram1 ram2)"
  proof (cases "before vs ram1 ram2")
    from d have "ram2 \<notin> set (fst (splitAt ram2 vs))" by (auto del: notI)
    then have h1: "ram2 \<notin> set (snd (splitAt ram1 (fst (splitAt ram2 vs))))"
      by (auto dest: splitAt_in_fst)
    case True with d p h1 show ?thesis by (auto del: notI)
  next
    from p have p2: "pre_between vs ram2 ram1" by (auto intro: pre_between_symI)
    case False with p have "before vs ram2 ram1" by auto
    with d p2 show ?thesis  by (auto del: notI)
  qed
next
  assume d:"distinct vs"
  case False then have p: "\<not> pre_between vs ram1 ram2" by auto
  then show ?thesis
  proof (cases "ram1 = ram2")
    case True with d have h1:"ram2 \<notin> set (snd (splitAt ram2 vs))" by (auto del: notI)
    from True d have h2: "ram2 \<notin> set (fst (splitAt ram2 (fst (splitAt ram2 vs))))" by (auto del: notI)
    with True d h1 show ?thesis by (auto simp: between_def split_def)
  next
    case False then have neq: "ram1 \<noteq> ram2" by auto
    then show ?thesis
    proof (cases "ram2 \<notin> set vs")
      case True with d show ?thesis
        by (auto dest: splitAt_no_ram splitAt_in_fst
         splitAt_in_fst simp: between_def split_def)
    next
      case False then have r1in: "ram2 \<in> set vs" by auto
      then show ?thesis
      proof (cases "ram1 \<notin> set vs")
        from d have h1: "ram1 \<notin> set (fst (splitAt ram1 vs))" by (auto del: notI)
        case True with d h1 show ?thesis by  (auto dest: splitAt_ram splitAt_no_ram simp: between_def split_def del: notI)
      next
        case False then have r2in: "ram1 \<in> set vs" by auto
        with d neq r1in have "pre_between vs ram1 ram2" by (auto simp: pre_between_def)
        with p show ?thesis by auto
      qed
    qed
  qed
qed

lemma between_distinct[intro]:
  "distinct vs \<Longrightarrow> distinct (between vs ram1 ram2)"
proof -
  assume vs: "distinct vs"
  define a where "a = fst (splitAt ram1 vs)"
  define b where "b = snd (splitAt ram1 vs)"
  from a_def b_def have ab: "(a,b) = splitAt ram1 vs" by auto
  with vs have ab_disj:"set a \<inter> set b = {}" by (drule_tac splitAt_distinct_ab)  auto
  define c where "c = fst (splitAt ram2 a)"
  define d where "d = snd (splitAt ram2 a)"
  from c_def d_def have c_d: "(c,d) = splitAt ram2 a" by auto
  with ab_disj have "set c \<inter> set b = {}" by (drule_tac splitAt_subset_ab) auto
  with vs a_def b_def c_def show ?thesis
    by (auto simp: between_def split_def splitAt_no_ram dest: splitAt_ram intro: splitAt_distinct_fst splitAt_distinct_snd)
qed

lemma between_distinct_r12:
  "distinct vs \<Longrightarrow> ram1 \<noteq> ram2 \<Longrightarrow> distinct (ram1 # between vs ram1 ram2 @ [ram2])" by (auto del: notI)

lemma between_vs:
  "before vs ram1 ram2 \<Longrightarrow> pre_between vs ram1 ram2 \<Longrightarrow>
  vs = fst (splitAt ram1 vs) @ ram1 # (between vs ram1 ram2) @ ram2 # snd (splitAt ram2 vs)"
  apply (simp) apply (frule pre_between_dist) apply (drule before_vs) by auto

lemma between_in:
  "before vs ram1 ram2 \<Longrightarrow> pre_between vs ram1 ram2 \<Longrightarrow> x \<in> set vs \<Longrightarrow> x = ram1 \<or> x \<in> set (between vs ram1 ram2) \<or> x = ram2 \<or> x \<in> set (between vs ram2 ram1)"
proof -
  assume b: "before vs ram1 ram2" and p: "pre_between vs ram1 ram2" and xin: "x \<in> set vs"
  define a where "a = fst (splitAt ram1 vs)"
  define b where "b = between vs ram1 ram2"
  define c where "c = snd (splitAt ram2 vs)"
  from p have "distinct vs" by auto
  from p b a_def b_def c_def have "vs = a @ ram1 # b @ ram2 # c" apply (drule_tac between_vs)  by auto
  with xin have "x \<in> set (a @ ram1 # b @ ram2 # c)" by auto
  then have "x \<in> set (a) \<or> x \<in> set (ram1 #b) \<or> x \<in> set (ram2 # c)" by auto
  then have "x \<in> set (a) \<or> x = ram1 \<or> x \<in> set b \<or> x = ram2 \<or> x \<in> set c" by auto
  then have "x \<in> set c \<or> x \<in> set (a) \<or> x = ram1 \<or> x \<in> set b \<or> x = ram2" by auto
  then have "x \<in> set (c @ a) \<or> x = ram1 \<or> x \<in> set b \<or> x = ram2" by auto
  with b p a_def b_def c_def show ?thesis by auto
qed

lemma
  "before vs ram1 ram2 \<Longrightarrow> pre_between vs ram1 ram2 \<Longrightarrow>
  hd vs \<noteq> ram1 \<Longrightarrow> (a,b) = splitAt (hd vs) (between vs ram2 ram1) \<Longrightarrow>
  vs = [hd vs] @ b @ [ram1] @ (between vs ram1 ram2) @ [ram2] @ a"
proof -
  assume b: "before vs ram1 ram2" and p: "pre_between vs ram1 ram2" and vs: "hd vs \<noteq> ram1" and ab: "(a,b) = splitAt (hd vs) (between vs ram2 ram1)"
  from p have dist_b: "distinct (between vs ram2 ram1)" by (auto intro: between_distinct simp: pre_between_def)
  with ab have "distinct a \<and> distinct b" by (auto intro: splitAt_distinct_a splitAt_distinct_b)
  define r where "r = snd (splitAt ram1 vs)"
  define btw where "btw = between vs ram2 ram1"
  from p r_def have vs2: "vs = fst (splitAt ram1 vs) @ [ram1] @ r" by (auto dest: splitAt_ram simp: pre_between_def)
  then have "fst (splitAt ram1 vs) = [] \<Longrightarrow> hd vs = ram1" by auto
  with vs have neq: "fst (splitAt ram1 vs) \<noteq> []" by auto
  with vs2 have vs_fst: "hd vs = hd (fst (splitAt ram1 vs))" by (induct ("fst (splitAt ram1 vs)")) auto
  with neq have "hd vs \<in> set (fst (splitAt ram1 vs))"  by auto
  with b p have "hd vs \<in> set (between vs ram2 ram1)" by auto
  with btw_def have help1: "btw =  fst (splitAt (hd vs) btw) @ [hd vs] @ snd (splitAt (hd vs) btw)" by (auto dest: splitAt_ram)
  from p b btw_def have "btw = snd (splitAt ram2 vs) @  fst (splitAt ram1 vs)" by auto
  with neq have "btw = snd (splitAt ram2 vs) @ hd (fst (splitAt ram1 vs)) # tl (fst (splitAt ram1 vs))" by auto
  with vs_fst have "btw = snd (splitAt ram2 vs) @ [hd vs] @ tl (fst (splitAt ram1 vs))" by auto
  with help1 have eq: "snd (splitAt ram2 vs) @ [hd vs] @ tl (fst (splitAt ram1 vs)) = fst (splitAt (hd vs) btw) @ [hd vs] @ snd (splitAt (hd vs) btw)" by auto
  from dist_b btw_def help1 have "distinct (fst (splitAt (hd vs) btw) @ [hd vs] @ snd (splitAt (hd vs) btw))" by auto
  with eq have  eq2: "snd (splitAt ram2 vs) = fst (splitAt (hd vs) btw) \<and> tl (fst (splitAt ram1 vs)) = snd (splitAt (hd vs) btw)" apply (rule_tac dist_at) by auto
  with btw_def ab have a: "a = snd (splitAt ram2 vs)" by (auto dest: pairD)
  from eq2 vs_fst have "hd (fst (splitAt ram1 vs)) # tl (fst (splitAt ram1 vs)) = hd vs # snd (splitAt (hd vs) btw)" by auto
  with ab btw_def neq have hdb: "hd vs # b = fst (splitAt ram1 vs)"  by (auto dest: pairD)

  from b p have "vs = fst (splitAt ram1 vs) @ [ram1] @ fst (splitAt ram2 (snd (splitAt ram1 vs))) @ [ram2] @ snd (splitAt ram2 vs)" apply simp
    apply (rule_tac before_vs) by (auto simp: pre_between_def)
  with hdb have "vs = (hd vs # b) @ [ram1] @ fst (splitAt ram2 (snd (splitAt ram1 vs))) @ [ram2] @ snd (splitAt ram2 vs)" by auto
  with a b p show ?thesis by (simp)
qed

lemma between_congs: "pre_between vs ram1 ram2 \<Longrightarrow> vs \<cong> vs' \<Longrightarrow> between vs ram1 ram2 = between vs' ram1 ram2"
proof -
  have "\<And> us. pre_between us ram1 ram2 \<Longrightarrow> before us ram1 ram2 \<Longrightarrow> between us ram1 ram2 = between (rotate1 us) ram1 ram2"
  proof -
    fix us
    assume vors: "pre_between us ram1 ram2"  "before us ram1 ram2"
    then have pb2: "pre_between (rotate1 us) ram1 ram2" by auto
    with vors show "between us ram1 ram2 = between (rotate1 us) ram1 ram2"
    proof (cases "us")
      case Nil then show ?thesis by auto
    next
      case (Cons u' us')
      with vors pb2 show ?thesis apply (auto simp: before_def)
        apply (case_tac "a") apply auto
        by (simp_all add: between_def split_def pre_between_def)
    qed
  qed

  moreover have "\<And> us. pre_between us ram1 ram2 \<Longrightarrow> before us ram2 ram1 \<Longrightarrow> between us ram1 ram2 = between (rotate1 us) ram1 ram2"
  proof -
    fix us
    assume vors: " pre_between us ram1 ram2"  "before us ram2 ram1"
    then have pb2: "pre_between (rotate1 us) ram1 ram2" by auto
    with vors show "between us ram1 ram2 = between (rotate1 us) ram1 ram2"
    proof (cases "us")
      case Nil then show ?thesis by auto
    next
      case (Cons u' us')
      with vors pb2 show ?thesis apply (auto simp: before_def)
        apply (case_tac "a") apply auto
        by (simp_all add: between_def split_def pre_between_def)
    qed
  qed

  ultimately have "help": "\<And> us. pre_between us ram1 ram2 \<Longrightarrow> between us ram1 ram2 = between (rotate1 us) ram1 ram2"
    apply (subgoal_tac "before us ram1 ram2 \<or> before us ram2 ram1") by auto

  assume "vs \<cong> vs'" and pre_b: "pre_between vs ram1 ram2"
  then obtain n where vs': "vs' = rotate n vs" by (auto simp: congs_def)
  have "between vs ram1 ram2 = between (rotate n vs) ram1 ram2"
  proof (induct n)
    case 0 then show ?case by auto
  next
    case (Suc m) then show ?case apply simp
      apply (subgoal_tac " between (rotate1 (rotate m vs)) ram1 ram2 = between (rotate m vs) ram1 ram2")
      by (auto intro: "help" [symmetric] pre_b)
  qed
  with vs' show ?thesis by auto
qed

lemma between_inter_empty:
 "pre_between vs ram1 ram2 \<Longrightarrow>
  set (between vs ram1 ram2) \<inter> set (between vs ram2 ram1) = {}"
apply (case_tac "before vs ram1 ram2")
 apply (simp add: pre_between_def)
 apply (elim conjE)
 apply (frule (1) before_vs)
 apply (subgoal_tac "distinct (fst (splitAt ram1 vs) @
          ram1 # fst (splitAt ram2 (snd (splitAt ram1 vs))) @ ram2 # snd (splitAt ram2 vs))")
  apply (thin_tac "vs = fst (splitAt ram1 vs) @
          ram1 # fst (splitAt ram2 (snd (splitAt ram1 vs))) @ ram2 # snd (splitAt ram2 vs)")
  apply (frule (1) before_dist_fst_snd)
  apply(simp)
  apply blast
 apply (simp only:)
apply (simp add: before_xor)
apply (subgoal_tac "pre_between vs ram2 ram1")
 apply (simp add: pre_between_def)
 apply (elim conjE)
 apply (frule (1) before_vs)
 apply (subgoal_tac "distinct (fst (splitAt ram2 vs) @
          ram2 # fst (splitAt ram1 (snd (splitAt ram2 vs))) @ ram1 # snd (splitAt ram1 vs))")
  apply (thin_tac "vs = fst (splitAt ram2 vs) @
          ram2 # fst (splitAt ram1 (snd (splitAt ram2 vs))) @ ram1 # snd (splitAt ram1 vs)")
  apply simp
  apply blast
 apply (simp only:)
by (rule pre_between_symI)


(*********************** between - is_nextElem *************************)
subsubsection \<open>\<open>between is_nextElem\<close>\<close>



lemma is_nextElem_or1: "pre_between vs ram1 ram2 \<Longrightarrow>
  is_nextElem vs x y \<Longrightarrow> before vs ram1 ram2 \<Longrightarrow>
  is_sublist [x,y] (ram1 # between vs ram1 ram2 @ [ram2])
 \<or>  is_sublist [x,y] (ram2 # between vs ram2 ram1 @ [ram1])"
proof -
  assume p: "pre_between vs ram1 ram2" and is_nextElem: "is_nextElem vs x y" and b: "before vs ram1 ram2"
  from p have r1: "ram1 \<in> set vs" by (auto simp: pre_between_def)
  define bs where "bs = [ram1] @ (between vs ram1 ram2) @ [ram2]"
  have rule1: "x \<in> set (ram1 # (between vs ram1 ram2)) \<Longrightarrow> is_sublist [x,y] bs"
  proof -
    assume xin:"x \<in> set (ram1 # (between vs ram1 ram2))"
    with bs_def have xin2: "x \<in> set bs" by auto
    define s where "s = snd (splitAt ram1 vs)"
    from r1 s_def have sub1:"is_sublist (ram1 # s) vs" by (auto intro: splitAt_is_sublist2R)
    from b p s_def have "ram2 \<in> set s" by (auto intro!: before_dist_r2 simp: pre_between_def)
    then have "is_prefix (fst (splitAt ram2 s) @ [ram2]) s" by (auto intro!: splitAt_is_prefix)
    then have "is_prefix ([ram1] @ ((fst (splitAt ram2 s)) @ [ram2])) ([ram1] @ s)" by (rule_tac is_prefix_add) auto
    with sub1 have "is_sublist (ram1 # (fst (splitAt ram2 s)) @ [ram2]) vs" apply (rule_tac is_sublist_trans) apply (rule is_prefix_sublist)
      by simp_all
    with p b s_def bs_def have subl: "is_sublist bs vs" by (auto)
    with p have db: "distinct bs" by (auto simp: pre_between_def)
    with xin bs_def have xnlb:"x \<noteq> last bs" by auto
    with p is_nextElem subl xin2 show "is_sublist [x,y] bs" apply (rule_tac is_sublist_is_nextElem) by (auto simp: pre_between_def)
  qed
  define bs2 where "bs2 = [ram2] @ (between vs ram2 ram1) @ [ram1]"
  have rule2: "x \<in> set (ram2 # (between vs ram2 ram1)) \<Longrightarrow> is_sublist [x,y] bs2"
  proof -
    assume xin:"x \<in> set (ram2 # (between vs ram2 ram1))"
    with bs2_def have xin2: "x \<in> set bs2" by auto
    define cs1 where "cs1 = ram2 # snd (splitAt ram2 vs)"
    then have cs1ne: "cs1 \<noteq> []" by auto
    define cs2 where "cs2 = fst (splitAt ram1 vs)"
    define cs2ram1 where "cs2ram1 = cs2 @ [ram1]"
    from cs1_def cs2_def bs2_def p b have bs2: "bs2 = cs1 @ cs2 @ [ram1]" by (auto simp: pre_between_def)
    have "x \<in> set cs1 \<Longrightarrow> x \<noteq> last cs1 \<Longrightarrow> is_sublist [x,y] cs1"
    proof-
      assume xin2: "x \<in> set cs1" and xnlcs1: "x \<noteq> last cs1"
      from cs1_def p have "is_sublist cs1 vs" by (simp add: pre_between_def)
      with p is_nextElem xnlcs1  xin2 show ?thesis  apply (rule_tac is_sublist_is_nextElem) by (auto simp: pre_between_def)
    qed
    with bs2 have incs1nl: "x \<in> set cs1 \<Longrightarrow> x \<noteq> last cs1 \<Longrightarrow> is_sublist [x,y] bs2"
      apply (auto simp: is_sublist_def) apply (intro exI)
      apply (subgoal_tac "as @ x # y # bs @ cs2 @ [ram1] = as @ x # y # (bs @ cs2 @ [ram1])")
      apply assumption by auto
    have "x = last cs1 \<Longrightarrow> y = hd (cs2 @ [ram1])"
    proof -
      assume xl: "x = last cs1"
      from p have "distinct vs" by auto
      with p have "vs = fst (splitAt ram2 vs) @ ram2 # snd (splitAt ram2 vs)" by (auto intro: splitAt_ram)
      with cs1_def have "last vs = last (fst (splitAt ram2 vs) @ cs1)" by auto
      with cs1ne have "last vs = last cs1" by auto
      with xl have "x = last vs" by auto
      with p is_nextElem have yhd: "y = hd vs" by auto
      from p have "vs = fst (splitAt ram1 vs) @ ram1 # snd (splitAt ram1 vs)" by (auto intro: splitAt_ram)
      with yhd cs2ram1_def cs2_def have yhd2: "y = hd (cs2ram1 @ snd (splitAt ram1 vs))" by auto
      from cs2ram1_def have "cs2ram1 \<noteq> []" by auto
      then have "hd (cs2ram1 @ snd(splitAt ram1 vs)) = hd (cs2ram1)" by auto
      with yhd2 cs2ram1_def show ?thesis by auto
    qed
    with bs2 cs1ne have "x = last cs1 \<Longrightarrow> is_sublist [x,y] bs2"
      apply (auto simp: is_sublist_def) apply (intro exI)
      apply (subgoal_tac "cs1 @ cs2 @ [ram1] = butlast cs1 @ last cs1 # hd (cs2 @ [ram1]) # tl (cs2 @ [ram1])")
      apply assumption by auto
    with incs1nl have incs1: "x \<in> set cs1 \<Longrightarrow> is_sublist [x,y] bs2" by auto
    have "x \<in> set cs2 \<Longrightarrow> is_sublist [x,y] (cs2 @ [ram1])"
    proof-
      assume xin2': "x \<in> set cs2"
      then have xin2: "x \<in> set (cs2 @ [ram1])" by auto
      define fr2 where "fr2 = snd (splitAt ram1 vs)"
      from p have "vs = fst (splitAt ram1 vs) @ ram1 # snd (splitAt ram1 vs)" by (auto intro: splitAt_ram)
      with fr2_def cs2_def have "vs = cs2 @ [ram1] @ fr2" by simp
      with p xin2'  have "x \<noteq> ram1" by (auto simp: pre_between_def)
      then have  xnlcs2: "x \<noteq> last (cs2 @ [ram1])" by auto
      from cs2_def p have "is_sublist (cs2 @ [ram1]) vs" by (simp add: pre_between_def)
      with p is_nextElem xnlcs2  xin2 show ?thesis  apply (rule_tac is_sublist_is_nextElem) by (auto simp: pre_between_def)
    qed
    with bs2 have "x \<in> set cs2 \<Longrightarrow> is_sublist [x,y] bs2"
      apply (auto simp: is_sublist_def) apply (intro exI)
      apply (subgoal_tac "cs1 @ as @ x # y # bs = (cs1 @ as) @ x # y # bs")
      apply assumption by auto
    with p b cs1_def cs2_def incs1 xin show ?thesis by auto
  qed
  from is_nextElem have "x \<in> set vs" by auto
  with b p have "x = ram1 \<or> x \<in> set (between vs ram1 ram2) \<or> x = ram2 \<or> x \<in> set (between vs ram2 ram1)" by (rule_tac between_in) auto
  then have "x \<in> set (ram1 # (between vs ram1 ram2)) \<or> x \<in> set (ram2 # (between vs ram2 ram1))" by auto
  with rule1 rule2 bs_def bs2_def show ?thesis by auto
qed


lemma is_nextElem_or: "pre_between vs ram1 ram2 \<Longrightarrow> is_nextElem vs x y \<Longrightarrow>
  is_sublist [x,y] (ram1 # between vs ram1 ram2 @ [ram2]) \<or>  is_sublist [x,y] (ram2 # between vs ram2 ram1 @ [ram1])"
proof (cases "before vs ram1 ram2")
  case True
  assume "pre_between vs ram1 ram2" "is_nextElem vs x y"
  with True show ?thesis by (rule_tac is_nextElem_or1)
next
  assume p: "pre_between vs ram1 ram2" and is_nextElem: "is_nextElem vs x y"
  from p have p': "pre_between vs ram2 ram1" by (auto intro: pre_between_symI)
  case False with p have "before vs ram2 ram1" by auto
  with p' is_nextElem show ?thesis apply (drule_tac is_nextElem_or1) apply assumption+ by auto
qed


lemma(*<*) between_eq2: (*>*)
  "pre_between vs ram1 ram2 \<Longrightarrow>
  before vs ram2 ram1 \<Longrightarrow>
   \<exists>as bs cs. between vs ram1 ram2 = cs @ as \<and> vs = as @[ram2] @ bs @ [ram1] @ cs"
  apply (subgoal_tac "pre_between vs ram2 ram1")
  apply auto apply (intro exI conjI) apply simp  apply (simp add: pre_between_def) apply auto
  apply (frule_tac before_vs) apply auto by (auto simp: pre_between_def)

lemma is_sublist_same_len[simp]:
 "length xs = length ys \<Longrightarrow> is_sublist xs ys = (xs = ys)"
apply(cases xs)
 apply simp
apply(rename_tac a as)
apply(cases ys)
 apply simp
apply(rename_tac b bs)
apply(case_tac "a = b")
 apply(subst is_sublist_rec)
 apply simp
apply simp
done


lemma is_nextElem_between_empty[simp]:
 "distinct vs \<Longrightarrow> is_nextElem vs a b \<Longrightarrow> between vs a b = []"
apply (simp add: is_nextElem_def between_def split_def)
apply (cases "vs") apply simp+
apply (simp split: if_split_asm)
apply (case_tac "b = aa")
 apply (simp add: is_sublist_def)
 apply (erule disjE)
  apply (elim exE)
  apply (case_tac "as")
   apply simp
  apply simp
 apply simp
 apply (case_tac "list" rule: rev_exhaust)
  apply simp
 apply simp
apply simp
apply (subgoal_tac "aa # list = vs")
 apply (thin_tac "vs = aa # list")
 apply simp
 apply (subgoal_tac "distinct vs")
  apply (simp add: is_sublist_def)
  apply (elim exE)
  by auto


lemma is_nextElem_between_empty': "between vs a b = [] \<Longrightarrow> distinct vs \<Longrightarrow> a \<in> set vs \<Longrightarrow> b \<in> set vs  \<Longrightarrow>
  a \<noteq> b \<Longrightarrow> is_nextElem vs a b"
apply (simp add: is_nextElem_def between_def split_def split: if_split_asm)
 apply (case_tac vs) apply simp
 apply simp
 apply (rule conjI)
  apply (rule impI)
  apply simp
 apply (case_tac "aa = b")
  apply simp
  apply (rule impI)
  apply (case_tac "list" rule: rev_exhaust)
   apply simp
  apply simp
  apply (case_tac "a = y") apply simp
  apply simp
  apply (elim conjE)
  apply (drule split_list_first)
  apply (elim exE)
  apply simp
 apply (rule impI)
 apply (subgoal_tac "b \<noteq> aa")
  apply simp
  apply (case_tac "a = aa")
   apply simp
   apply (case_tac "list") apply simp
   apply simp
   apply (case_tac "aaa = b") apply (simp add: is_sublist_def) apply force
   apply simp
  apply simp
  apply (drule split_list_first)
  apply (elim exE)
  apply simp
  apply (case_tac "zs") apply simp
  apply simp
  apply (case_tac "aaa = b")
   apply simp
   apply (simp add: is_sublist_def) apply force
  apply simp
 apply force
apply (case_tac vs) apply simp
apply simp
apply (rule conjI)
 apply (rule impI) apply simp
apply (rule impI)
apply (case_tac "b = aa")
 apply simp
 apply (case_tac "list" rule: rev_exhaust) apply simp
 apply simp
 apply (case_tac "a = y") apply simp
 apply simp
 apply (drule split_list_first)
 apply (elim exE)
 apply simp
apply simp apply (case_tac "a = aa") by auto


lemma between_nextElem: "pre_between vs u v \<Longrightarrow>
 between vs u (nextElem vs (hd vs) v) = between vs u v @ [v]"
apply(subgoal_tac "pre_between vs v u")
 prefer 2 apply (clarsimp simp add:pre_between_def)
apply(case_tac "before vs u v")
apply(drule (1) between_eq2)
 apply(clarsimp simp:pre_between_def hd_append split:list.split)
 apply(simp add:between_def split_def)
 apply(fastforce simp:neq_Nil_conv)
apply (simp only:before_xor)
apply(drule (1) between_eq2)
apply(clarsimp simp:pre_between_def hd_append split:list.split)
apply (simp add: append_eq_Cons_conv)
apply(fastforce simp:between_def split_def)
done



(******************** section split_face ********************************)

lemma nextVertices_in_face[simp]: "v \<in> \<V> f \<Longrightarrow> f\<^bsup>n\<^esup> \<bullet> v \<in> \<V> f"
proof -
  assume v: "v \<in> \<V> f"
  then have f: "vertices f \<noteq> []" by auto
  show ?thesis apply (simp add: nextVertices_def)
    apply (induct n) by (auto simp: f v)
qed



subsubsection \<open>\<open>is_nextElem edges\<close> equivalence\<close>


lemma is_nextElem_edges1: "distinct (vertices f) \<Longrightarrow> (a,b) \<in> edges (f::face) \<Longrightarrow> is_nextElem (vertices f) a b" apply (simp add: edges_face_def nextVertex_def) apply (rule is_nextElem1) by auto


lemma is_nextElem_edges2:
 "distinct (vertices f) \<Longrightarrow> is_nextElem (vertices f) a b \<Longrightarrow>
 (a,b) \<in> edges (f::face)"
apply (auto simp add: edges_face_def nextVertex_def)
apply (rule sym)
apply (rule is_nextElem2) by (auto  intro: is_nextElem_a)

lemma is_nextElem_edges_eq[simp]:
 "distinct (vertices (f::face)) \<Longrightarrow>
 (a,b) \<in> edges f = is_nextElem (vertices f) a b"
by (auto intro: is_nextElem_edges1 is_nextElem_edges2)



(*********************** nextVertex *****************************)
subsubsection \<open>@{const nextVertex}\<close>

lemma nextElem_suc2: "distinct (vertices f) \<Longrightarrow> last (vertices f) = v \<Longrightarrow> v \<in> set (vertices f) \<Longrightarrow> f \<bullet> v = hd (vertices f)"
proof -
  assume dist: "distinct (vertices f)" and last: "last (vertices f) = v" and v: "v \<in> set (vertices f)"
  define ls where "ls = vertices f"
  have ind: "\<And> c. distinct ls \<Longrightarrow> last ls = v \<Longrightarrow> v \<in> set ls \<Longrightarrow> nextElem ls c v = c"
  proof (induct ls)
    case Nil then show ?case by auto
  next
    case (Cons m ms)
    then show ?case
    proof (cases "m = v")
      case True with Cons have "ms = []"  apply (cases ms rule: rev_exhaust) by auto
      then show ?thesis by auto
    next
      case False with Cons have a1: "v \<in> set ms" by auto
      then have ms: "ms \<noteq> []" by auto

      with False Cons ms have "nextElem ms c v = c" apply (rule_tac Cons) by simp_all
      with False ms show ?thesis by simp
    qed
  qed
  from dist ls_def last v have "nextElem ls (hd ls) v = hd ls" apply (rule_tac ind) by auto
  with ls_def show ?thesis by (simp add: nextVertex_def)
qed


(*********************** split_face ****************************)
subsection \<open>@{const split_face}\<close>


definition pre_split_face :: "face \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> bool" where
"pre_split_face oldF ram1 ram2 newVertexList \<equiv>
   distinct (vertices oldF) \<and> distinct (newVertexList)
  \<and> \<V> oldF \<inter> set newVertexList = {}
  \<and> ram1 \<in> \<V> oldF \<and> ram2 \<in> \<V> oldF \<and> ram1 \<noteq> ram2"

declare pre_split_face_def [simp]


lemma pre_split_face_p_between[intro]:
  "pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow> pre_between (vertices oldF) ram1 ram2"  by (simp add: pre_between_def)

lemma pre_split_face_symI:
  "pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow> pre_split_face oldF ram2 ram1 newVertexList" by auto


lemma pre_split_face_rev[intro]:
  "pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow> pre_split_face oldF ram1 ram2 (rev newVertexList)" by auto

lemma split_face_distinct1:
  "(f12, f21) = split_face oldF ram1 ram2 newVertexList \<Longrightarrow> pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow>
    distinct (vertices f12)"
proof -
  assume split: "(f12, f21) = split_face oldF ram1 ram2 newVertexList" and p: "pre_split_face oldF ram1 ram2 newVertexList"
  define old_vs where "old_vs = vertices oldF"
  with p have d_old_vs: "distinct old_vs" by auto
  from p have p2: "pre_between (vertices oldF) ram1 ram2" by auto
  have rule1: "before old_vs ram1 ram2 \<Longrightarrow> distinct (vertices f12)"
  proof -
    assume b: "before old_vs ram1 ram2"
    with split p have "f12 = Face (rev newVertexList @ ram1 # between (vertices oldF) ram1 ram2 @ [ram2]) Nonfinal" by (simp add: split_face_def)
    then have h1:"vertices f12 = rev newVertexList @ ram1 # between (vertices oldF) ram1 ram2 @ [ram2]" by auto
    from p have d1: "distinct(ram1 # between (vertices oldF) ram1 ram2 @ [ram2])" by (auto del: notI)
    from b p p2 old_vs_def have d2: "set (ram1 # between (vertices oldF) ram1 ram2 @ [ram2]) \<inter> set newVertexList = {}"
      by (auto dest!: splitAt_in_fst splitAt_in_snd)
    with h1 d1 p show ?thesis by auto
  qed
  have rule2: "before old_vs ram2 ram1 \<Longrightarrow> distinct (vertices f12)"
  proof -
    assume b: "before old_vs ram2 ram1"
    from p have p3: "pre_split_face oldF ram1 ram2 newVertexList"
       by (auto intro: pre_split_face_symI)
    then have p4: "pre_between (vertices oldF) ram2 ram1" by auto
    with split p have
     "f12 = Face (rev newVertexList @ ram1 # between (vertices oldF) ram1 ram2 @ [ram2]) Nonfinal"
      by (simp add: split_face_def)
    then have h1:"vertices f12 = rev newVertexList @ ram1 # between (vertices oldF) ram1 ram2 @ [ram2]"
      by auto
    from p3 have d1: "distinct(ram1 # between (vertices oldF) ram1 ram2 @ [ram2])"
    by (auto del: notI)
    from b p3 p4 old_vs_def
    have d2: "set (ram1 # between (vertices oldF) ram1 ram2 @ [ram2]) \<inter> set newVertexList = {}"
      by auto
    with h1 d1 p show ?thesis by auto
  qed
  from p2 rule1 rule2 old_vs_def show ?thesis by auto
qed

lemma split_face_distinct1'[intro]:
  "pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow>
    distinct (vertices (fst(split_face oldF ram1 ram2 newVertexList)))"
apply (rule_tac split_face_distinct1)
  by (auto simp del: pre_split_face_def simp: split_face_def)

lemma split_face_distinct2:
  "(f12, f21) = split_face oldF ram1 ram2 newVertexList \<Longrightarrow>
   pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow> distinct (vertices f21)"
proof -
  assume split: "(f12, f21) = split_face oldF ram1 ram2 newVertexList"
    and p: "pre_split_face oldF ram1 ram2 newVertexList"
  define old_vs where "old_vs = vertices oldF"
  with p have d_old_vs: "distinct old_vs" by auto
  with p have p1: "pre_split_face oldF ram1 ram2 newVertexList" by auto
  from p have p2: "pre_between (vertices oldF) ram1 ram2" by auto
  have rule1: "before old_vs ram1 ram2 \<Longrightarrow> distinct (vertices f21)"
  proof -
    assume b: "before old_vs ram1 ram2"
    with split p
    have "f21 = Face (ram2 # between (vertices oldF) ram2 ram1 @ [ram1] @ newVertexList) Nonfinal"
      by (simp add: split_face_def)
    then have h1:"vertices f21 = ram2 # between (vertices oldF) ram2 ram1 @ [ram1] @ newVertexList"
      by auto
    from p have d1: "distinct(ram1 # between (vertices oldF) ram2 ram1 @ [ram2])"
       by (auto del: notI)
    from b p1 p2 old_vs_def
    have d2: "set (ram2 # between (vertices oldF) ram2 ram1 @ [ram1]) \<inter> set newVertexList = {}"
      by auto
    with h1 d1 p1 show ?thesis by auto
  qed
  have rule2: "before old_vs ram2 ram1 \<Longrightarrow> distinct (vertices f21)"
  proof -
    assume b: "before old_vs ram2 ram1"
    from p have p3: "pre_split_face oldF ram1 ram2 newVertexList"
      by (auto intro: pre_split_face_symI)
    then have p4: "pre_between (vertices oldF) ram2 ram1" by auto
    with split p
    have "f21 = Face (ram2 # between (vertices oldF) ram2 ram1 @ [ram1] @ newVertexList) Nonfinal"
      by (simp add: split_face_def)
    then have h1:"vertices f21 = ram2 # between (vertices oldF) ram2 ram1 @ [ram1] @ newVertexList"
      by auto
    from p3 have d1: "distinct(ram2 # between (vertices oldF) ram2 ram1 @ [ram1])"
      by (auto del: notI)
    from b p3 p4 old_vs_def
    have d2: "set (ram2 # between (vertices oldF) ram2 ram1 @ [ram1]) \<inter> set newVertexList = {}"
      by auto
    with h1 d1 p1 show ?thesis by auto
  qed
  from p2 rule1 rule2 old_vs_def show ?thesis by auto
qed

lemma split_face_distinct2'[intro]:
  "pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow> distinct (vertices (snd(split_face oldF ram1 ram2 newVertexList)))"
apply (rule_tac split_face_distinct2) by (auto simp del: pre_split_face_def simp: split_face_def)


declare pre_split_face_def [simp del]

lemma split_face_edges_or: "(f12, f21) = split_face oldF ram1 ram2 newVertexList \<Longrightarrow> pre_split_face oldF ram1 ram2 newVertexList \<Longrightarrow> (a, b) \<in> edges oldF \<Longrightarrow> (a,b) \<in> edges f12 \<or> (a,b) \<in> edges f21"
proof -
  assume nf: "(f12, f21) = split_face oldF ram1 ram2 newVertexList" and p: "pre_split_face oldF ram1 ram2 newVertexList" and old:"(a, b) \<in> edges oldF"
  from p have d1:"distinct (vertices oldF)" by auto
  from nf p have d2: "distinct (vertices f12)" by (auto dest: pairD)
  from nf p have d3: "distinct (vertices f21)" by (auto dest: pairD)
  from p have p': "pre_between (vertices oldF) ram1 ram2" by auto
  from old d1 have is_nextElem: "is_nextElem (vertices oldF) a b" by simp
  with p have "is_sublist [a,b] (ram1 # (between (vertices oldF) ram1 ram2) @ [ram2]) \<or> is_sublist [a,b] (ram2 # (between (vertices oldF) ram2 ram1) @ [ram1])" apply (rule_tac is_nextElem_or) by auto
  then have "is_nextElem (rev newVertexList @ ram1 # between (vertices oldF) ram1 ram2 @ [ram2]) a b
    \<or> is_nextElem (ram2 # between (vertices oldF) ram2 ram1 @ ram1 # newVertexList) a b"
  proof (cases "is_sublist [a,b] (ram1 # (between (vertices oldF) ram1 ram2) @ [ram2])")
    case True then show ?thesis by (auto dest: is_sublist_add intro!: is_nextElem_sublistI)
  next
    case False
    assume "is_sublist [a,b] (ram1 # (between (vertices oldF) ram1 ram2) @ [ram2])
      \<or> is_sublist [a,b] (ram2 # (between (vertices oldF) ram2 ram1) @ [ram1])"
    with False have "is_sublist [a,b] (ram2 # (between (vertices oldF) ram2 ram1) @ [ram1])" by auto
    then show ?thesis apply (rule_tac disjI2) apply (rule_tac is_nextElem_sublistI)
      apply (subgoal_tac "is_sublist [a, b] ([] @ (ram2 # between (vertices oldF) ram2 ram1 @ [ram1]) @ newVertexList)") apply force by (frule is_sublist_add)
  qed
  with nf d1 d2 d3 show ?thesis by (simp add: split_face_def)
qed


subsection \<open>\<open>verticesFrom\<close>\<close>

definition verticesFrom :: "face \<Rightarrow> vertex \<Rightarrow> vertex list" where
 "verticesFrom f \<equiv> rotate_to (vertices f)"

lemmas verticesFrom_Def = verticesFrom_def rotate_to_def

lemma len_vFrom[simp]:
 "v \<in> \<V> f \<Longrightarrow> |verticesFrom f v| = |vertices f|"
apply(drule split_list_first)
apply(clarsimp simp: verticesFrom_Def)
done

lemma verticesFrom_empty[simp]:
 "v \<in> \<V> f \<Longrightarrow> (verticesFrom f v = []) = (vertices f = [])"
by(clarsimp simp: verticesFrom_Def)

lemma verticesFrom_congs:
 "v \<in> \<V> f \<Longrightarrow> (vertices f) \<cong> (verticesFrom f v)"
by(simp add:verticesFrom_def cong_rotate_to)

lemma verticesFrom_eq_if_vertices_cong:
  "\<lbrakk>distinct(vertices f); distinct(vertices f'); 
    vertices f \<cong> vertices f'; x \<in> \<V> f \<rbrakk> \<Longrightarrow>
   verticesFrom f x = verticesFrom f' x"
by(clarsimp simp:congs_def verticesFrom_Def splitAt_rotate_pair_conv)


lemma verticesFrom_in[intro]: "v \<in> \<V> f \<Longrightarrow> a \<in> \<V> f \<Longrightarrow> a \<in> set (verticesFrom f v)"
by (auto dest: verticesFrom_congs congs_pres_nodes)

lemma verticesFrom_in': "a \<in> set (verticesFrom f v) \<Longrightarrow> a \<noteq> v \<Longrightarrow> a \<in> \<V> f"
  apply (cases "v \<in> \<V> f") apply (auto dest: verticesFrom_congs congs_pres_nodes)
  by (simp add: verticesFrom_Def)

lemma set_verticesFrom:
 "v \<in> \<V> f \<Longrightarrow> set (verticesFrom f v) = \<V> f"
apply(auto)
apply (auto simp add: verticesFrom_Def)
done

lemma verticesFrom_hd: "hd (verticesFrom f v) = v" by (simp add: verticesFrom_Def)

lemma verticesFrom_distinct[simp]: "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> distinct (verticesFrom f v)" apply (frule_tac verticesFrom_congs) by (auto simp: congs_distinct)

lemma verticesFrom_nextElem_eq:
 "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> u \<in> \<V> f \<Longrightarrow>
 nextElem (verticesFrom f v) (hd (verticesFrom f v)) u
 = nextElem (vertices f) (hd (vertices f)) u" apply (subgoal_tac "(verticesFrom f v) \<cong> (vertices f)")
 apply (rule nextElem_congs_eq) apply (auto simp: verticesFrom_congs congs_pres_nodes) apply (rule congs_sym)
 by (simp add: verticesFrom_congs)

lemma nextElem_vFrom_suc1: "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> i < length (vertices f) \<Longrightarrow> last (verticesFrom f v) \<noteq> u \<Longrightarrow> (verticesFrom f v)!i = u \<Longrightarrow> f \<bullet> u = (verticesFrom f v)!(Suc i)"
proof -
  assume dist: "distinct (vertices f)" and ith: "(verticesFrom f v)!i = u" and small_i: "i < length (vertices f)" and notlast: "last (verticesFrom f v) \<noteq> u" and v: "v \<in> \<V> f"
  hence eq: "(vertices f) \<cong> (verticesFrom f v)" by (auto simp: verticesFrom_congs)
  from ith eq small_i have "u \<in> set (verticesFrom f v)" by (auto simp: congs_length)
  with eq have u: "u \<in> \<V> f" by (auto simp: congs_pres_nodes)
  define ls where "ls = verticesFrom f v"
  with dist ith have "ls!i = u" by auto
  have ind: "\<And> c i. i < length ls \<Longrightarrow> distinct ls \<Longrightarrow> last ls \<noteq> u \<Longrightarrow> ls!i = u \<Longrightarrow> u \<in> set ls \<Longrightarrow>
     nextElem ls c u = ls ! Suc i"
  proof (induct ls)
    case Nil then show ?case by auto
  next
    case (Cons m ms)
    then show ?case
    proof (cases "m = u")
      case True with Cons have "u \<notin> set ms" by auto
      with Cons True have i: "i = 0" apply (induct i) by auto
      with Cons show ?thesis  apply (simp split: if_split_asm) apply (cases ms) by simp_all
    next
      case False with Cons have a1: "u \<in> set ms" by auto
      then have ms: "ms \<noteq> []" by auto
      from False Cons have i: "0 < i" by auto
      define i' where "i' = i - 1"
      with i have i': "i = Suc i'" by auto
      with False Cons i' ms have "nextElem ms c u = ms ! Suc i'" apply (rule_tac Cons) by simp_all
      with False Cons i' ms show ?thesis by simp
    qed
  qed
  from eq dist ith ls_def small_i notlast v
  have "nextElem ls (hd ls) u = ls ! Suc i"
    apply (rule_tac ind) by (auto simp: congs_length)
  with dist u v ls_def show ?thesis by (simp add: nextVertex_def verticesFrom_nextElem_eq)
qed

lemma verticesFrom_nth: "distinct (vertices f) \<Longrightarrow> d < length (vertices f) \<Longrightarrow>
  v \<in> \<V> f \<Longrightarrow> (verticesFrom f v)!d = f\<^bsup>d\<^esup> \<bullet> v"
proof (induct d)
  case 0 then show ?case by (simp add: verticesFrom_Def nextVertices_def)
next
  case (Suc n)
  then have dist2: "distinct (verticesFrom f v)"
     apply (frule_tac verticesFrom_congs) by (auto simp: congs_distinct)
  from Suc have in2: "v \<in> set (verticesFrom f v)"
     apply (frule_tac verticesFrom_congs) by (auto dest: congs_pres_nodes)
  then have vFrom: "(verticesFrom f v) = butlast (verticesFrom f v) @ [last (verticesFrom f v)]"
    apply (cases "(verticesFrom f v)" rule: rev_exhaust) by auto
  from Suc show ?case
  proof (cases "last (verticesFrom f v) = f\<^bsup>n\<^esup> \<bullet> v")
    case True with Suc have "verticesFrom f v ! n = f\<^bsup>n\<^esup> \<bullet> v" by (rule_tac Suc) auto
    with True have "last (verticesFrom f v) = verticesFrom f v ! n" by auto
    with Suc dist2 in2 have "Suc n = length (verticesFrom f v)"
      apply (rule_tac nth_last_Suc_n) by auto
    with Suc show ?thesis by auto
  next
    case False with Suc show ?thesis apply (simp add: nextVertices_def) apply (rule sym)
    apply (rule_tac nextElem_vFrom_suc1) by simp_all
  qed
qed


lemma verticesFrom_length: "distinct (vertices f) \<Longrightarrow> v \<in> set (vertices f) \<Longrightarrow>
  length (verticesFrom f v) = length (vertices f)"
by (auto intro: congs_length verticesFrom_congs)

lemma verticesFrom_between: "v' \<in> \<V> f \<Longrightarrow> pre_between (vertices f) u v \<Longrightarrow>
  between (vertices f) u v = between (verticesFrom f v') u v"
by (auto intro!: between_congs verticesFrom_congs)


lemma verticesFrom_is_nextElem: "v \<in> \<V> f \<Longrightarrow>
   is_nextElem (vertices f) a b = is_nextElem (verticesFrom f v) a b"
    apply (rule is_nextElem_congs_eq) by (rule verticesFrom_congs)

lemma verticesFrom_is_nextElem_last: "v' \<in> \<V> f \<Longrightarrow> distinct (vertices f)
  \<Longrightarrow> is_nextElem (verticesFrom f v') (last (verticesFrom f v')) v  \<Longrightarrow> v = v'"
apply (subgoal_tac "distinct (verticesFrom f v')")
apply (subgoal_tac "last (verticesFrom f v') \<in> set (verticesFrom f v')")
apply (simp add: nextElem_is_nextElem)
apply (simp add: verticesFrom_hd)
apply (cases "(verticesFrom f v')" rule: rev_exhaust) apply (simp add: verticesFrom_Def)
by auto

lemma  verticesFrom_is_nextElem_hd: "v' \<in> \<V> f \<Longrightarrow> distinct (vertices f)
  \<Longrightarrow> is_nextElem (verticesFrom f v') u v' \<Longrightarrow> u = last (verticesFrom f v')"
apply (subgoal_tac "distinct (verticesFrom f v')")
apply (thin_tac "distinct (vertices f)") apply (auto simp: is_nextElem_def)
apply (drule is_sublist_y_hd) apply (simp add: verticesFrom_hd)
by auto

lemma verticesFrom_pres_nodes1: "v \<in> \<V> f \<Longrightarrow> \<V> f = set(verticesFrom f v)"
proof -
  assume "v \<in> \<V> f"
  then have "fst (splitAt v (vertices f)) @ [v] @ snd (splitAt v (vertices f)) = vertices f"
    apply (drule_tac splitAt_ram) by simp
  moreover have "set (fst (splitAt v (vertices f)) @ [v] @ snd (splitAt v (vertices f))) = set (verticesFrom f v)"
    by (auto simp: verticesFrom_Def)
  ultimately show ?thesis by simp
qed

lemma verticesFrom_pres_nodes: "v \<in> \<V> f \<Longrightarrow> w \<in> \<V> f \<Longrightarrow> w \<in> set (verticesFrom f v)"
by (auto dest: verticesFrom_pres_nodes1)


lemma before_verticesFrom: "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> w \<in> \<V> f \<Longrightarrow>
  v \<noteq> w \<Longrightarrow> before (verticesFrom f v) v w"
proof -
  assume v: "v \<in> \<V> f" and w: "w \<in> \<V> f" and neq: "v \<noteq> w"
  have "hd (verticesFrom f v) = v" by (rule verticesFrom_hd)
  with v have vf:"verticesFrom f v = v # tl (verticesFrom f v)"
    apply (frule_tac verticesFrom_pres_nodes1)
    apply (cases "verticesFrom f v") by auto
  moreover with v w have "w \<in> set (verticesFrom f v)" by (auto simp: verticesFrom_pres_nodes)
  ultimately have "w \<in> set (v # tl (verticesFrom f v))" by auto
  with neq have "w \<in> set (tl (verticesFrom f v))" by auto
  with vf have "verticesFrom f v =
    [] @ v # fst (splitAt w (tl (verticesFrom f v))) @ w # snd (splitAt w (tl (verticesFrom f v)))"
    by (auto dest: splitAt_ram)
  then show ?thesis apply (unfold before_def) by (intro exI)
qed

lemma last_vFrom:
 "\<lbrakk> distinct(vertices f); x \<in> \<V> f \<rbrakk> \<Longrightarrow> last(verticesFrom f x) = f\<^bsup>-1\<^esup> \<bullet> x"
apply(frule split_list)
apply(clarsimp simp:prevVertex_def verticesFrom_Def split:list.split)
done


lemma rotate_before_vFrom:
  "\<lbrakk> distinct(vertices f); r \<in> \<V> f; r\<noteq>u \<rbrakk> \<Longrightarrow>
   before (verticesFrom f r) u v \<Longrightarrow> before (verticesFrom f v) r u"
using [[linarith_neq_limit = 1]]
apply(frule split_list)
apply(clarsimp simp:verticesFrom_Def)
apply(rename_tac as bs)
apply(clarsimp simp:before_def)
apply(rename_tac xs ys zs)
apply(subst (asm) Cons_eq_append_conv)
apply clarsimp
apply(rename_tac bs')
apply(subst (asm) append_eq_append_conv2)
apply clarsimp
apply(rename_tac as')
apply(erule disjE)
 defer
 apply clarsimp
 apply(rule_tac x = "v#zs" in exI)
 apply(rule_tac x = "bs@as'" in exI)
 apply simp
apply clarsimp
apply(subst (asm) append_eq_Cons_conv)
apply(erule disjE)
apply clarsimp
apply(rule_tac x = "v#zs" in exI)
apply simp apply blast
apply clarsimp
apply(rename_tac ys')
apply(subst (asm) append_eq_append_conv2)
apply clarsimp
apply(rename_tac vs')
apply(erule disjE)
 apply clarsimp
 apply(subst (asm) append_eq_Cons_conv)
 apply(erule disjE)
  apply clarsimp
  apply(rule_tac x = "v#zs" in exI)
  apply simp apply blast
 apply clarsimp
 apply(rule_tac x = "v#ys'@as" in exI)
 apply simp apply blast
apply clarsimp
apply(rule_tac x = "v#zs" in exI)
apply simp apply blast
done

lemma before_between:
 "\<lbrakk> before(verticesFrom f x) y z; distinct(vertices f); x \<in> \<V> f; x \<noteq> y \<rbrakk> \<Longrightarrow>
  y \<in> set(between (vertices f) x z)"
apply(induct f)
apply(clarsimp simp:verticesFrom_Def before_def)
apply(frule split_list)
apply(clarsimp simp:Cons_eq_append_conv)
apply(subst (asm) append_eq_append_conv2)
apply clarsimp
apply(erule disjE)
 apply(clarsimp simp:append_eq_Cons_conv)
 prefer 2 apply(clarsimp simp add:between_def split_def)
apply(erule disjE)
 apply (clarsimp simp:between_def split_def)
apply clarsimp
apply(subst (asm) append_eq_append_conv2)
apply clarsimp
apply(erule disjE)
 prefer 2 apply(clarsimp simp add:between_def split_def)
apply(clarsimp simp:append_eq_Cons_conv)
apply(fastforce simp:between_def split_def)
done

lemma before_between2:
 "\<lbrakk> before (verticesFrom f u) v w; distinct(vertices f); u \<in> \<V> f \<rbrakk>
  \<Longrightarrow> u = v \<or> u \<in> set (between (vertices f) w v)"
apply(subgoal_tac "pre_between (vertices f) v w")
 apply(subst verticesFrom_between)
   apply assumption
  apply(erule pre_between_symI)
 apply(frule pre_between_r1)
 apply(drule (1) verticesFrom_distinct)
 using verticesFrom_hd[of f u]
 apply(clarsimp simp add:before_def between_def split_def hd_append
                split:if_split_asm)
apply(frule (1) verticesFrom_distinct)
apply(clarsimp simp:pre_between_def before_def simp del:verticesFrom_distinct)
apply(rule conjI)
 apply(cases "v = u")
  apply simp
 apply(rule verticesFrom_in'[of v f u])apply simp apply assumption
apply(cases "w = u")
 apply simp
apply(rule verticesFrom_in'[of w f u])apply simp apply assumption
done


(************************** splitFace ********************************)


subsection \<open>@{const splitFace}\<close>


definition pre_splitFace :: "graph \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> vertex list \<Rightarrow> bool" where
  "pre_splitFace g ram1 ram2 oldF nvs \<equiv>
  oldF \<in> \<F> g \<and> \<not> final oldF \<and> distinct (vertices oldF) \<and> distinct nvs
  \<and> \<V> g \<inter> set nvs = {}
  \<and> \<V> oldF \<inter> set nvs = {}
  \<and> ram1 \<in> \<V> oldF \<and> ram2 \<in> \<V> oldF
  \<and> ram1 \<noteq> ram2
  \<and> (((ram1,ram2) \<notin> edges oldF \<and> (ram2,ram1) \<notin> edges oldF
     \<and> (ram1, ram2) \<notin> edges g \<and> (ram2, ram1) \<notin> edges g) \<or> nvs \<noteq> [])"

declare pre_splitFace_def [simp]

lemma pre_splitFace_pre_split_face[simp]:
  "pre_splitFace g ram1 ram2 oldF nvs \<Longrightarrow> pre_split_face oldF ram1 ram2 nvs"
 by (simp add: pre_splitFace_def pre_split_face_def)

lemma pre_splitFace_oldF[simp]:
  "pre_splitFace g ram1 ram2 oldF nvs \<Longrightarrow> oldF \<in> \<F> g"
  apply (unfold pre_splitFace_def) by force

declare pre_splitFace_def [simp del]

lemma splitFace_split_face:
     "oldF \<in> \<F> g \<Longrightarrow>
     (f\<^sub>1, f\<^sub>2, newGraph) = splitFace g ram\<^sub>1 ram\<^sub>2 oldF newVs \<Longrightarrow>
     (f\<^sub>1, f\<^sub>2) = split_face oldF ram\<^sub>1 ram\<^sub>2 newVs"
  by (simp add: splitFace_def split_def)


(* split_face *)
lemma split_face_empty_ram2_ram1_in_f12:
  "pre_split_face oldF ram1 ram2 [] \<Longrightarrow>
  (f12, f21) = split_face oldF ram1 ram2 [] \<Longrightarrow> (ram2, ram1) \<in> edges f12"
proof -
  assume split: "(f12, f21) = split_face oldF ram1 ram2 []"
  "pre_split_face oldF ram1 ram2 []"
  then have "ram2 \<in> \<V> f12" by (simp add: split_face_def)
  moreover with split have "f12 \<bullet> ram2 = hd (vertices f12)"
   apply (rule_tac nextElem_suc2)
   apply (simp add: pre_split_face_def split_face_distinct1)
   by (simp add: split_face_def)
  with split have "ram1 = f12 \<bullet> ram2"
   by (simp add: split_face_def)
  ultimately show ?thesis by (simp add: edges_face_def)
qed

lemma split_face_empty_ram2_ram1_in_f12':
  "pre_split_face oldF ram1 ram2 [] \<Longrightarrow>
  (ram2, ram1) \<in> edges (fst (split_face oldF ram1 ram2 []))"
proof -
  assume split: "pre_split_face oldF ram1 ram2 []"
  define f12 where "f12 = fst (split_face oldF ram1 ram2 [])"
  define f21 where "f21 = snd (split_face oldF ram1 ram2 [])"
  then have "(f12, f21) = split_face oldF ram1 ram2 []" by (simp add: f12_def f21_def)
  with split have "(ram2, ram1) \<in> edges f12"
    by (rule split_face_empty_ram2_ram1_in_f12)
  with f12_def show ?thesis by simp
qed

lemma splitFace_empty_ram2_ram1_in_f12:
  "pre_splitFace g ram1 ram2 oldF [] \<Longrightarrow>
  (f12, f21, newGraph) = splitFace g ram1 ram2 oldF [] \<Longrightarrow>
  (ram2, ram1) \<in> edges f12"
proof -
  assume pre: "pre_splitFace g ram1 ram2 oldF []"
  then have oldF: "oldF \<in> \<F> g" by (unfold pre_splitFace_def) simp
  assume sp: "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF []"
  with oldF have "(f12, f21) = split_face oldF ram1 ram2 []"
    by (rule splitFace_split_face)

  with pre sp show ?thesis
  apply (unfold  splitFace_def pre_splitFace_def)
  apply (simp add: split_def)
  apply (rule split_face_empty_ram2_ram1_in_f12')
  apply (rule pre_splitFace_pre_split_face)
  apply (rule pre)
  done
qed

lemma splitFace_f12_new_vertices:
  "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs \<Longrightarrow>
  v \<in> set  newVs \<Longrightarrow> v \<in> \<V> f12"
  apply (unfold splitFace_def)
  apply (simp add: split_def)
  apply (unfold split_face_def Let_def)
  by simp


lemma splitFace_add_vertices_direct[simp]:
"vertices (snd (snd (splitFace g ram1 ram2 oldF [countVertices g ..< countVertices g + n])))
  = vertices g @ [countVertices g ..< countVertices g + n]"
  apply (auto simp: splitFace_def split_def) apply (cases g)
  apply auto  apply (induct n) by auto

lemma splitFace_delete_oldF:
" (f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVertexList \<Longrightarrow>
 oldF \<noteq> f12 \<Longrightarrow> oldF \<noteq> f21 \<Longrightarrow> distinct (faces g) \<Longrightarrow>
 oldF \<notin> \<F> newGraph"
by (simp add: splitFace_def split_def distinct_set_replace)

lemma splitFace_faces_1:
"(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVertexList \<Longrightarrow>
oldF \<in> \<F> g \<Longrightarrow>
set (faces newGraph) \<union> {oldF} = {f12, f21} \<union> set (faces g)"
(is "?oldF \<Longrightarrow> ?C \<Longrightarrow> ?A = ?B")
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> ?A" and "?C" and "?oldF"
  then show "x \<in> ?B" apply (simp add: splitFace_def split_def) by (auto dest: replace1)
next
  fix x
  assume "x \<in> ?B" and "?C" and "?oldF"
  then show "x \<in> ?A" apply (simp add: splitFace_def split_def)
    apply (cases "x = oldF") apply simp_all
    apply (cases "x = f12")  apply simp_all
    apply (cases "x = f21")  by (auto intro: replace3 replace4)
qed


lemma splitFace_distinct1[intro]:"pre_splitFace g ram1 ram2 oldF newVertexList \<Longrightarrow>
  distinct (vertices (fst (snd (splitFace g ram1 ram2 oldF newVertexList))))"
  apply (unfold  splitFace_def split_def)
  by (auto simp add: split_def)

lemma splitFace_distinct2[intro]:"pre_splitFace g ram1 ram2 oldF newVertexList \<Longrightarrow>
  distinct (vertices (fst (splitFace g ram1 ram2 oldF newVertexList)))"
  apply (unfold  splitFace_def split_def)
  by (auto simp add: split_def)


lemma splitFace_add_f21': "f' \<in> \<F> g' \<Longrightarrow> fst (snd (splitFace g' v a f' nvl))
           \<in> \<F> (snd (snd (splitFace g' v a f' nvl)))"
apply (simp add: splitFace_def split_def) apply (rule disjI2)
apply (rule replace3) by simp_all

lemma split_face_help[simp]: "Suc 0 < |vertices (fst (split_face f' v a nvl))|"
  by (simp add: split_face_def)

lemma split_face_help'[simp]: "Suc 0 < |vertices (snd (split_face f' v a nvl))|"
 by (simp add: split_face_def)

lemma splitFace_split: "f \<in> \<F> (snd (snd (splitFace g v a f' nvl))) \<Longrightarrow>
  f \<in> \<F> g
  \<or>  f = fst (splitFace g v a f' nvl)
  \<or>  f = (fst (snd (splitFace g v a f' nvl)))"
 apply (simp add: splitFace_def split_def)
 apply safe by (frule replace5)  simp

lemma pre_FaceDiv_between1: "pre_splitFace g' ram1 ram2 f [] \<Longrightarrow>
  \<not> between (vertices f) ram1 ram2 = []"
proof -
  assume pre_f: "pre_splitFace g' ram1 ram2 f []"
  then have pre_bet: "pre_between (vertices f) ram1 ram2" apply (unfold pre_splitFace_def)
    by (simp add: pre_between_def)
  then have pre_bet': "pre_between (verticesFrom f ram1) ram1 ram2"
    by (simp add: pre_between_def set_verticesFrom)
  from pre_f have dist': "distinct (verticesFrom f ram1)" apply (unfold pre_splitFace_def) by simp
  from pre_f have ram2: "ram2 \<in> \<V> f" apply (unfold pre_splitFace_def) by simp
  from pre_f have "\<not> is_nextElem (vertices f) ram1 ram2" apply (unfold pre_splitFace_def) by auto
  with pre_f have "\<not> is_nextElem (verticesFrom f ram1) ram1 ram2" apply (unfold pre_splitFace_def)
    by (simp add: verticesFrom_is_nextElem [symmetric])
  moreover
  from pre_f have "ram2 \<in> set (verticesFrom f ram1)" apply (unfold pre_splitFace_def) by auto
  moreover
  from pre_f have "ram2 \<noteq>  ram1" apply (unfold pre_splitFace_def) by auto
  ultimately have ram2_not: "ram2 \<noteq>  hd (snd (splitAt ram1 (vertices f)) @ fst (splitAt ram1 (vertices f)))"
    apply (simp add: is_nextElem_def verticesFrom_Def)
    apply (cases "snd (splitAt ram1 (vertices f)) @ fst (splitAt ram1 (vertices f))")
    apply simp apply simp
    apply (simp add: is_sublist_def) by auto


  from pre_f have before: "before (verticesFrom f ram1) ram1 ram2" apply (unfold pre_splitFace_def)
    apply safe apply (rule before_verticesFrom) by auto
  have "fst (splitAt ram2 (snd (splitAt ram1 (verticesFrom f ram1)))) = [] \<Longrightarrow> False"
  proof -
    assume  "fst (splitAt ram2 (snd (splitAt ram1 (verticesFrom f ram1)))) = []"
    moreover
    from ram2 pre_f have "ram2 \<in> set (verticesFrom f ram1)"apply (unfold pre_splitFace_def)
      by auto
    with pre_f have "ram2 \<in> set (snd (splitAt ram1 (vertices f)) @ fst (splitAt ram1 (vertices f)))"
      apply (simp add: verticesFrom_Def)
      apply (unfold pre_splitFace_def)  by auto
    moreover
    note dist'
    ultimately  have "ram2 = hd (snd (splitAt ram1 (vertices f)) @ fst (splitAt ram1 (vertices f)))"
      apply (rule_tac ccontr)
      apply (cases "(snd (splitAt ram1 (vertices f)) @ fst (splitAt ram1 (vertices f)))")
      apply simp
      apply simp
      by (simp add: verticesFrom_Def del: distinct_append)
    with ram2_not show ?thesis by auto
  qed
  with before pre_bet' have  "between (verticesFrom f ram1) ram1 ram2 \<noteq>  []" by auto
  with pre_f pre_bet show ?thesis apply (unfold pre_splitFace_def) apply safe
  by (simp add: verticesFrom_between)
qed

lemma pre_FaceDiv_between2: "pre_splitFace g' ram1 ram2 f [] \<Longrightarrow>
  \<not> between (vertices f) ram2 ram1 = []"
proof -
  assume pre_f: "pre_splitFace g' ram1 ram2 f []"
  then have "pre_splitFace g' ram2 ram1 f []" apply (unfold pre_splitFace_def) by auto
  then show ?thesis by (rule pre_FaceDiv_between1)
qed


(********************** Edges *******************)

definition Edges :: "vertex list \<Rightarrow> (vertex \<times> vertex) set" where
"Edges vs \<equiv> {(a,b). is_sublist [a,b] vs}"

lemma Edges_Nil[simp]: "Edges [] = {}"
by(simp add:Edges_def is_sublist_def)

lemma Edges_rev:
 "Edges (rev (zs::vertex list)) = {(b,a). (a,b) \<in> Edges zs}"
  by (auto simp add: Edges_def is_sublist_rev)

lemma in_Edges_rev[simp]:
 "((a,b) : Edges (rev (zs::vertex list))) = ((b,a) \<in> Edges zs)"
by (simp add: Edges_rev)

lemma notinset_notinEdge1: "x \<notin> set xs \<Longrightarrow> (x,y) \<notin> Edges xs"
by(unfold Edges_def)(blast intro:is_sublist_in)

lemma notinset_notinEdge2: "y \<notin> set xs \<Longrightarrow> (x,y) \<notin> Edges xs"
by(unfold Edges_def)(blast intro:is_sublist_in1)

lemma in_Edges_in_set: "(x,y) : Edges vs \<Longrightarrow> x \<in> set vs \<and> y \<in> set vs"
by(unfold Edges_def)(blast intro:is_sublist_in is_sublist_in1)


lemma edges_conv_Edges:
  "distinct(vertices(f::face)) \<Longrightarrow> \<E> f =
   Edges (vertices f) \<union>
  (if vertices f = [] then {} else {(last(vertices f), hd(vertices f))})"
by(induct f) (auto simp: Edges_def is_nextElem_def)


lemma Edges_Cons: "Edges(x#xs) =
  (if xs = [] then {} else Edges xs \<union> {(x,hd xs)})"
apply(auto simp:Edges_def)
   apply(rule ccontr)
   apply(simp)
  apply(erule thin_rl)
  apply(erule contrapos_np)
  apply(clarsimp simp:is_sublist_def Cons_eq_append_conv)
  apply(rename_tac as bs)
  apply(erule disjE)
   apply simp
  apply(clarsimp)
  apply(rename_tac cs)
  apply(rule_tac x = cs in exI)
  apply(rule_tac x = bs in exI)
  apply(rule HOL.refl)
 apply(clarsimp simp:neq_Nil_conv)
 apply(subst is_sublist_rec)
 apply simp
apply(simp add:is_sublist_def)
apply(erule exE)+
apply(rename_tac as bs)
apply simp
apply(rule_tac x = "x#as" in exI)
apply(rule_tac x = bs in exI)
apply simp
done

lemma Edges_append: "Edges(xs @ ys) =
  (if xs = [] then Edges ys else
   if ys = [] then Edges xs else
   Edges xs \<union> Edges ys \<union> {(last xs, hd ys)})"
apply(induct xs)
 apply simp
apply (simp add:Edges_Cons)
apply blast
done


lemma Edges_rev_disj: "distinct xs \<Longrightarrow> Edges(rev xs) \<inter> Edges(xs) = {}"
apply(induct xs)
 apply simp
apply(auto simp:Edges_Cons Edges_append last_rev
      notinset_notinEdge1 notinset_notinEdge2)
done

lemma disj_sets_disj_Edges:
 "set xs \<inter> set ys = {} \<Longrightarrow> Edges xs \<inter> Edges ys = {}"
by(unfold Edges_def)(blast intro:is_sublist_in is_sublist_in1)

lemma disj_sets_disj_Edges2:
 "set ys \<inter> set xs = {} \<Longrightarrow> Edges xs \<inter> Edges ys = {}"
by(blast intro!:disj_sets_disj_Edges)


lemma finite_Edges[iff]: "finite(Edges xs)"
by(induct xs)(simp_all add:Edges_Cons)


lemma Edges_compl:
 "\<lbrakk> distinct vs; x \<in> set vs; y \<in> set vs; x \<noteq> y \<rbrakk> \<Longrightarrow>
 Edges(x # between vs x y @ [y]) \<inter> Edges(y # between vs y x @ [x]) = {}"
using [[linarith_neq_limit = 1]]
apply(subgoal_tac
 "\<And>xs (ys::vertex list). xs \<noteq> [] \<Longrightarrow> set xs \<inter> set ys = {} \<Longrightarrow> hd xs \<notin> set ys")
 prefer 2 apply(drule hd_in_set) apply(blast)
apply(frule split_list[of  x])
apply clarsimp
apply(erule disjE)
 apply(frule split_list[of y])
 apply(clarsimp simp add:between_def split_def)
 apply (clarsimp simp add:Edges_Cons Edges_append
    notinset_notinEdge1 notinset_notinEdge2
    disj_sets_disj_Edges disj_sets_disj_Edges2
    Int_Un_distrib Int_Un_distrib2)
 apply(fastforce)
apply(frule split_list[of y])
apply(clarsimp simp add:between_def split_def)
apply (clarsimp simp add:Edges_Cons Edges_append notinset_notinEdge1
 notinset_notinEdge2 disj_sets_disj_Edges disj_sets_disj_Edges2
 Int_Un_distrib Int_Un_distrib2)
apply fastforce
done

lemma Edges_disj:
 "\<lbrakk> distinct vs; x \<in> set vs; z \<in> set vs; x \<noteq> y; y \<noteq> z;
    y \<in> set(between vs x z) \<rbrakk> \<Longrightarrow>
 Edges(x # between vs x y @ [y]) \<inter> Edges(y # between vs y z @ [z]) = {}"
apply(subgoal_tac
 "\<And>xs (ys::vertex list). xs \<noteq> [] \<Longrightarrow> set xs \<inter> set ys = {} \<Longrightarrow> hd xs \<notin> set ys")
 prefer 2 apply(drule hd_in_set) apply(blast)
apply(frule split_list[of x])
apply clarsimp
apply(erule disjE)
 apply simp
 apply(drule inbetween_inset)
 apply(rule Edges_compl)
    apply simp
   apply simp
  apply simp
 apply simp
apply(erule disjE)
 apply(frule split_list[of z])
 apply(clarsimp simp add:between_def split_def)
 apply(erule disjE)
  apply(frule split_list[of y])
  apply clarsimp
  apply (clarsimp simp add:Edges_Cons Edges_append
    notinset_notinEdge1 notinset_notinEdge2
    disj_sets_disj_Edges disj_sets_disj_Edges2
    Int_Un_distrib Int_Un_distrib2)
  apply fastforce
 apply(frule split_list[of y])
 apply clarsimp
 apply (clarsimp simp add:Edges_Cons Edges_append notinset_notinEdge1
 notinset_notinEdge2 disj_sets_disj_Edges disj_sets_disj_Edges2
 Int_Un_distrib Int_Un_distrib2)
 apply fastforce
apply(frule split_list[of z])
apply(clarsimp simp add:between_def split_def)
apply(frule split_list[of y])
apply clarsimp
apply (clarsimp simp add:Edges_Cons Edges_append notinset_notinEdge1
 notinset_notinEdge2 disj_sets_disj_Edges disj_sets_disj_Edges2
 Int_Un_distrib Int_Un_distrib2)
apply fastforce
done

lemma edges_conv_Un_Edges:
 "\<lbrakk> distinct(vertices(f::face)); x \<in> \<V> f; y \<in> \<V> f; x \<noteq> y \<rbrakk> \<Longrightarrow>
  \<E> f = Edges(x # between (vertices f) x y @ [y]) \<union>
           Edges(y # between (vertices f) y x @ [x])"
apply(simp add:edges_conv_Edges)
apply(rule conjI)
 apply clarsimp
apply clarsimp
apply(frule split_list[of  x])
apply clarsimp
apply(erule disjE)
 apply(frule split_list[of y])
 apply(clarsimp simp add:between_def split_def)
 apply (clarsimp simp add:Edges_Cons Edges_append
    notinset_notinEdge1 notinset_notinEdge2
    disj_sets_disj_Edges disj_sets_disj_Edges2
    Int_Un_distrib Int_Un_distrib2)
 apply(fastforce)
apply(frule split_list[of y])
apply(clarsimp simp add:between_def split_def)
apply (clarsimp simp add:Edges_Cons Edges_append
    notinset_notinEdge1 notinset_notinEdge2
    disj_sets_disj_Edges disj_sets_disj_Edges2
    Int_Un_distrib Int_Un_distrib2)
apply(fastforce)
done


lemma Edges_between_edges:
  "\<lbrakk> (a,b) \<in> Edges (u # between (vertices(f::face)) u v @ [v]);
    pre_split_face f u v vs \<rbrakk> \<Longrightarrow> (a,b) \<in> \<E> f"
apply(simp add:pre_split_face_def)
apply(induct f)
apply(simp add:edges_conv_Edges Edges_Cons)
apply clarify
apply(rename_tac list)
apply(case_tac "between list u v = []")
 apply simp
 apply(drule (4) is_nextElem_between_empty')
 apply(simp add:Edges_def)
apply(subgoal_tac "pre_between list u v")
 prefer 2 apply (simp add:pre_between_def)
apply(subgoal_tac "pre_between list v u")
 prefer 2 apply (simp add:pre_between_def)
apply(case_tac "before list u v")
 apply(drule (1) between_eq2)
 apply clarsimp
 apply(erule disjE)
  apply (clarsimp simp:neq_Nil_conv)
  apply(rule is_nextElem_sublistI)
  apply(simp (no_asm) add:is_sublist_def)
  apply blast
 apply(rule is_nextElem_sublistI)
 apply(clarsimp simp add:Edges_def is_sublist_def)
 apply(rename_tac as bs cs xs ys)
 apply(rule_tac x = "as @ u # xs" in exI)
 apply(rule_tac x = "ys @ cs" in exI)
 apply simp
apply (simp only:before_xor)
apply(drule (1) between_eq2)
apply clarsimp
apply(rename_tac as bs cs)
apply(erule disjE)
 apply (clarsimp simp:neq_Nil_conv)
 apply(case_tac cs)
  apply clarsimp
  apply(simp add:is_nextElem_def)
 apply simp
 apply(rule is_nextElem_sublistI)
 apply(simp (no_asm) add:is_sublist_def)
 apply(rule_tac x = "as @ v # bs" in exI)
 apply simp
apply(rule_tac m1 = "|as|+1" in is_nextElem_rotate_eq[THEN iffD1])
apply simp
apply(simp add:rotate_drop_take)
apply(rule is_nextElem_sublistI)
apply(clarsimp simp add:Edges_def is_sublist_def)
apply(rename_tac xs ys)
apply(rule_tac x = "bs @ u # xs" in exI)
apply simp
done


(******************** split_face_edges ********************************)


(* split_face *)

lemma edges_split_face1: "pre_split_face f u v vs \<Longrightarrow>
 \<E>(fst(split_face f u v vs)) =
 Edges(v # rev vs @ [u]) \<union> Edges(u # between (vertices f) u v @ [v])"
apply(simp add: edges_conv_Edges split_face_distinct1')
apply(auto simp add:split_face_def Edges_Cons Edges_append)
done

lemma edges_split_face2: "pre_split_face f u v vs \<Longrightarrow>
 \<E>(snd(split_face f u v vs)) =
 Edges(u # vs @ [v]) \<union> Edges(v # between (vertices f) v u @ [u])"
apply(simp add: edges_conv_Edges split_face_distinct2')
apply(auto simp add:split_face_def Edges_Cons Edges_append)
done

lemma split_face_empty_ram1_ram2_in_f21:
  "pre_split_face oldF ram1 ram2 [] \<Longrightarrow>
  (f12, f21) = split_face oldF ram1 ram2 [] \<Longrightarrow> (ram1, ram2) \<in> edges f21"
proof -
  assume split: "(f12, f21) = split_face oldF ram1 ram2 []"
  "pre_split_face oldF ram1 ram2 []"
  then have "ram1 \<in> \<V> f21" by (simp add: split_face_def)
  moreover with split have "f21 \<bullet> ram1 = hd (vertices f21)"
   apply (rule_tac nextElem_suc2)
   apply (simp add: pre_split_face_def split_face_distinct2)
   by (simp add: split_face_def)
  with split have "ram2 = f21 \<bullet> ram1"
   by (simp add: split_face_def)
  ultimately show ?thesis by (simp add: edges_face_def)
qed

lemma split_face_empty_ram1_ram2_in_f21':
  "pre_split_face oldF ram1 ram2 [] \<Longrightarrow>
  (ram1, ram2) \<in> edges (snd (split_face oldF ram1 ram2 []))"
proof -
  assume split: "pre_split_face oldF ram1 ram2 []"
  define f12 where "f12 = fst (split_face oldF ram1 ram2 [])"
  define f21 where "f21 = snd (split_face oldF ram1 ram2 [])"
  then have "(f12, f21) = split_face oldF ram1 ram2 []" by (simp add: f12_def f21_def)
  with split have "(ram1, ram2) \<in> edges f21"
    by (rule split_face_empty_ram1_ram2_in_f21)
  with f21_def show ?thesis by simp
qed

lemma splitFace_empty_ram1_ram2_in_f21:
  "pre_splitFace g ram1 ram2 oldF [] \<Longrightarrow>
  (f12, f21, newGraph) = splitFace g ram1 ram2 oldF [] \<Longrightarrow>
  (ram1, ram2) \<in> edges f21"
proof -
  assume pre: "pre_splitFace g ram1 ram2 oldF []"
  then have oldF: "oldF \<in> \<F> g" by (unfold pre_splitFace_def) simp
  assume sp: "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF []"
  with oldF have "(f12, f21) = split_face oldF ram1 ram2 []"
    by (rule splitFace_split_face)

  with pre sp show ?thesis
  apply (unfold  splitFace_def pre_splitFace_def)
  apply (simp add: split_def)
  apply (rule split_face_empty_ram1_ram2_in_f21')
  apply (rule pre_splitFace_pre_split_face)
  apply (rule pre)
  done
qed

lemma splitFace_f21_new_vertices:
  "(f12, f21, newGraph) = splitFace g ram1 ram2 oldF newVs \<Longrightarrow>
  v \<in> set  newVs \<Longrightarrow> v \<in> \<V> f21"
  apply (unfold splitFace_def)
  apply (simp add: split_def)
  apply (unfold split_face_def)
  by simp

lemma split_face_edges_f12:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "(f12, f21) = split_face f ram1 ram2 vs"
              "vs \<noteq> []" "vs1 = between (vertices f) ram1 ram2" "vs1 \<noteq> []"
shows "edges f12 =
      {(hd vs, ram1) , (ram1, hd vs1), (last vs1, ram2), (ram2, last vs)} \<union>
      Edges(rev vs) \<union> Edges vs1" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f12)
    apply (case_tac "c = ram2 \<and> d = last vs") apply simp apply simp apply (elim exE)
    apply (case_tac "c = ram1") apply simp
     apply (subgoal_tac "between (vertices f) ram1 ram2 @ [ram2] = d # bs")
      apply (case_tac "between (vertices f) ram1 ram2") apply simp apply simp
     apply (rule dist_at2) apply (rule dist_f12) apply (rule sym) apply simp  apply simp
    (* c \<noteq> ram1 *)
    apply (case_tac "c \<in> set(rev vs)")
     apply (subgoal_tac "distinct(rev vs)") apply (simp only: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac "zs") apply simp
       apply (subgoal_tac "ys = as") apply(drule last_rev) apply (simp)
       apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp
       apply simp
      apply (simp add:rev_swap)
      apply (subgoal_tac "ys = as")
       apply (clarsimp simp add: Edges_def is_sublist_def)
       apply (rule conjI)
        apply (subgoal_tac "\<exists>as bs. rev list @ [d, c] = as @ d # c # bs") apply simp apply (intro exI) apply simp
       apply (subgoal_tac "\<exists>asa bs. rev list @ d # c # rev as = asa @ d # c # bs") apply simp  apply (intro exI) apply simp
      apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp
    apply (simp add: pre_split_face_def)
    (* c \<notin> set vs *)
    apply (case_tac "c \<in> set (between (vertices f) ram1 ram2)")
     apply (subgoal_tac "distinct (between (vertices f) ram1 ram2)") apply (simp add: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac zs) apply simp apply (subgoal_tac "rev vs @ ram1 # ys = as") apply force
       apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp
      apply simp
      apply (subgoal_tac "rev vs @ ram1 # ys = as") apply (simp add: Edges_def is_sublist_def)
       apply (subgoal_tac "(rev vs @ ram1 # ys) @ c # a # list @ [ram2] = as @ c # d # bs") apply simp
        apply (rule conjI) apply (rule impI) apply (rule disjI2)+ apply (rule exI) apply force
        apply (rule impI) apply (rule disjI2)+ apply force
       apply force
      apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp
     apply (thin_tac "rev vs @ ram1 # between (vertices f) ram1 ram2 @ [ram2] = as @ c # d # bs")
     apply (subgoal_tac "distinct (vertices f12)") apply simp
     apply (rule dist_f12)
      (* c \<notin>  set (between (vertices f) ram1 ram2) *)
    apply (subgoal_tac "c = ram2") apply simp
     apply (subgoal_tac "rev vs @ ram1 # between (vertices f) ram1 ram2 = as") apply force
     apply (rule dist_at1) apply (rule dist_f12) apply (rule sym)  apply simp apply simp

    (* c \<noteq> ram2 *)
    apply (subgoal_tac "c \<in> set (rev vs @ ram1 # between (vertices f) ram1 ram2 @ [ram2])")
     apply (thin_tac "rev vs @ ram1 # between (vertices f) ram1 ram2 @ [ram2] = as @ c # d # bs") apply simp
    by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f12 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    apply (case_tac "c = ram2 \<and> d = last vs") apply simp
    apply (rule disjCI) apply simp
    apply (case_tac "c = hd vs \<and> d = ram1")
     apply (case_tac "vs") apply simp
     apply force
    apply simp
    apply (case_tac "c = ram1 \<and> d = hd (between (vertices f) ram1 ram2)")
     apply (case_tac "between (vertices f) ram1 ram2") apply simp apply force
    apply simp
    apply (case_tac "c = last (between (vertices f) ram1 ram2) \<and> d = ram2")
     apply (case_tac "between (vertices f) ram1 ram2" rule: rev_exhaust) apply simp
     apply simp
     apply (intro exI) apply (subgoal_tac "rev vs @ ram1 # ys @ [y, ram2] = (rev vs @ ram1 # ys) @ y # ram2 # []")
      apply assumption
     apply simp
    apply simp
    apply (case_tac "(d,c) \<in> Edges vs") apply (simp add: Edges_def is_sublist_def)
     apply (elim exE) apply simp apply (intro exI) apply simp
    apply (simp add: Edges_def is_sublist_def)
    apply (elim exE) apply simp apply (intro exI)
    apply (subgoal_tac "rev vs @ ram1 # as @ c # d # bs @ [ram2] = (rev vs @ ram1 # as) @ c # d # bs @ [ram2]")
     apply assumption
    by simp
qed

lemma split_face_edges_f12_vs:
assumes vors: "pre_split_face f ram1 ram2 []"
              "(f12, f21) = split_face f ram1 ram2 []"
              "vs1 = between (vertices f) ram1 ram2" "vs1 \<noteq> []"
shows "edges f12 = {(ram2, ram1) , (ram1, hd vs1), (last vs1, ram2)} \<union>
                   Edges vs1" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f12)
    apply (case_tac " c = ram2 \<and> d = ram1") apply simp
    apply simp apply (elim exE)
    apply (case_tac "c = ram1") apply simp
     apply (subgoal_tac "as = []") apply simp
      apply (case_tac "between (vertices f) ram1 ram2") apply simp
      apply simp
     apply (rule dist_at1) apply (rule dist_f12) apply force apply (rule sym) apply simp
    (* a \<noteq> ram1 *)
    apply (case_tac "c \<in> set (between (vertices f) ram1 ram2)")
     apply (subgoal_tac "distinct (between (vertices f) ram1 ram2)") apply (simp add: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac zs) apply simp apply (subgoal_tac "ram1 # ys = as") apply force
       apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp
      apply simp
      apply (subgoal_tac "ram1 # ys = as") apply (simp add: Edges_def is_sublist_def)
       apply (subgoal_tac "(ram1 # ys) @ c # a # list @ [ram2] = as @ c # d # bs") apply simp
        apply (rule conjI) apply (rule impI) apply (rule disjI2)+ apply (rule exI) apply force
        apply (rule impI) apply (rule disjI2)+ apply force
       apply force
      apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp
     apply (thin_tac "ram1 # between (vertices f) ram1 ram2 @ [ram2] = as @ c # d # bs")
     apply (subgoal_tac "distinct (vertices f12)") apply simp
     apply (rule dist_f12)
      (* c \<notin>  set (between (vertices f) ram1 ram2) *)
    apply (subgoal_tac "c = ram2") apply simp
     apply (subgoal_tac "ram1 # between (vertices f) ram1 ram2 = as") apply force
     apply (rule dist_at1) apply (rule dist_f12) apply (rule sym)  apply simp apply simp

    (* c \<noteq> ram2 *)
    apply (subgoal_tac "c \<in> set (ram1 # between (vertices f) ram1 ram2 @ [ram2])")
     apply (thin_tac "ram1 # between (vertices f) ram1 ram2 @ [ram2] = as @ c # d # bs") apply simp
    by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f12 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    apply (case_tac "c = ram2 \<and> d = ram1") apply simp
    apply (rule disjCI) apply simp
    apply (case_tac "c = ram1 \<and> d = hd (between (vertices f) ram1 ram2)")
     apply (case_tac "between (vertices f) ram1 ram2") apply simp
     apply force
    apply simp
    apply (case_tac "c = last (between (vertices f) ram1 ram2) \<and> d = ram2")
     apply (case_tac "between (vertices f) ram1 ram2" rule: rev_exhaust) apply simp
     apply simp
     apply (intro exI) apply (subgoal_tac "ram1 # ys @ [y, ram2] = (ram1 # ys) @ y # ram2 # []")
      apply assumption
     apply simp
    apply simp
    apply (case_tac "(c, d) \<in> Edges vs") apply (simp add: Edges_def is_sublist_def)
     apply (elim exE) apply simp apply (intro exI)
     apply (subgoal_tac "ram1 # as @ c # d # bs @ [ram2] = (ram1 # as) @ c # d # (bs @ [ram2])") apply assumption
     apply simp
    apply (simp add: Edges_def is_sublist_def)
    apply (elim exE) apply simp apply (intro exI)
    apply (subgoal_tac "ram1 # as @ c # d # bs @ [ram2] = (ram1 # as) @ c # d # bs @ [ram2]")
     apply assumption
    by simp
qed

lemma split_face_edges_f12_bet:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "(f12, f21) = split_face f ram1 ram2 vs"
              "vs \<noteq> []" "between (vertices f) ram1 ram2 = []"
shows "edges f12 = {(hd vs, ram1) , (ram1, ram2), (ram2, last vs)} \<union>
                   Edges(rev vs)" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f12)
    apply (case_tac " c = ram2 \<and> d = last vs") apply simp
    apply simp apply (elim exE)
    apply (case_tac "c = ram1") apply simp
     apply (subgoal_tac "rev vs = as") apply simp
     apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp  apply simp
    (* a \<noteq> ram1 *)
    apply (case_tac "c \<in> set(rev vs)")
     apply (subgoal_tac "distinct(rev vs)") apply (simp only: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac "zs") apply simp apply (subgoal_tac "ys = as") apply (simp add:rev_swap)
       apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp apply simp
      apply (subgoal_tac "ys = as") apply (simp add: Edges_def is_sublist_def rev_swap)
       apply (rule conjI)
        apply (subgoal_tac "\<exists>as bs. rev list @ [d, c] = as @ d # c # bs") apply simp apply (intro exI) apply simp
       apply (subgoal_tac "\<exists>asa bs. rev list @ d # c # rev as = asa @ d # c # bs") apply simp  apply (intro exI) apply simp
      apply (rule dist_at1) apply (rule dist_f12) apply (rule sym) apply simp apply simp
     apply (simp add: pre_split_face_def)
    (* c \<notin> set vs *)
    apply (subgoal_tac "c = ram2") apply simp
     apply (subgoal_tac "rev vs @ [ram1] = as") apply force
     apply (rule dist_at1) apply (rule dist_f12) apply (rule sym)  apply simp apply simp

    (* c \<noteq> ram2 *)
    apply (subgoal_tac "c \<in> set (rev vs @ ram1 # [ram2])")
     apply (thin_tac "rev vs @ ram1 # [ram2] = as @ c # d # bs") apply simp
    by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f12 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    apply (case_tac "c = hd vs \<and> d = ram1")
     apply (case_tac "vs") apply simp
     apply force
    apply simp
    apply (case_tac "c = ram1 \<and> d = ram2") apply force
    apply simp
    apply (case_tac "c = ram2 \<and> d = last vs")
     apply (case_tac "vs" rule:rev_exhaust) apply simp
     apply simp
    apply (simp add: Edges_def is_sublist_def)
    apply (elim exE) apply simp apply (rule conjI)
     apply (rule impI) apply (rule disjI1) apply (intro exI)
     apply (subgoal_tac "c # d # rev as @ [ram1, ram2] = [] @ c # d # rev as @ [ram1,ram2]") apply assumption apply simp
    apply (rule impI) apply (rule disjI1) apply (intro exI) by simp
qed

lemma split_face_edges_f12_bet_vs:
assumes vors: "pre_split_face f ram1 ram2 []"
              "(f12, f21) = split_face f ram1 ram2 []"
              "between (vertices f) ram1 ram2 = []"
shows "edges f12 = {(ram2, ram1) , (ram1, ram2)}" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f12)
    apply (case_tac " c = ram2 \<and> d = ram1") apply force
    apply simp apply (elim exE)
    apply (case_tac "c = ram1")  apply simp
     apply (case_tac "as") apply simp
    apply (case_tac "list") apply simp apply simp
    apply (case_tac "as") apply simp apply (case_tac "list") apply simp by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f12: "distinct (vertices f12)" apply (rule_tac split_face_distinct1) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f12 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    by auto
qed


lemma split_face_edges_f12_subset: "pre_split_face f ram1 ram2 vs \<Longrightarrow>
  (f12, f21) = split_face f ram1 ram2 vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow>
  {(hd vs, ram1), (ram2, last vs)} \<union> Edges(rev vs) \<subseteq> edges f12"
  apply (case_tac "between (vertices f) ram1 ram2")
    apply (frule split_face_edges_f12_bet)  apply simp apply simp apply simp apply force
    apply (frule split_face_edges_f12) apply simp+ by force

(*declare in_Edges_rev [simp del] rev_eq_Cons_iff [simp del]*)

lemma split_face_edges_f21:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "(f12, f21) = split_face f ram1 ram2 vs"
              "vs \<noteq> []" "vs2 = between (vertices f) ram2 ram1" "vs2 \<noteq> []"
shows "edges f21 = {(last vs2, ram1) , (ram1, hd vs), (last vs, ram2), (ram2, hd vs2)} \<union>
  Edges vs \<union> Edges vs2" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f21)
    apply (case_tac " c = last vs \<and> d = ram2") apply simp
    apply simp apply (elim exE)
    apply (case_tac "c = ram1") apply simp
     apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 = as")
      apply clarsimp
     apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
    (* a \<noteq> ram1 *)
    apply (case_tac "c \<in> set vs")
     apply (subgoal_tac "distinct vs")
      apply (simp add: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac "zs") apply simp
       apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # ys = as") apply force
       apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
      apply simp
      apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # ys = as")
       apply (subgoal_tac "(ram2 # between (vertices f) ram2 ram1 @ ram1 # ys) @ c # a # list = as @ c # d # bs")
        apply (thin_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # ys @ c # a # list = as @ c # d # bs")
        apply (simp add: Edges_def is_sublist_def)
        apply(rule conjI)
         apply (subgoal_tac "\<exists>as bs. ys @ [c, d] = as @ c # d # bs") apply simp apply force
        apply force
       apply force
      apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
     apply (simp add: pre_split_face_def)
    (* c \<notin> set (rev vs) *)
    apply (case_tac "c \<in> set (between (vertices f) ram2 ram1)")
     apply (subgoal_tac "distinct (between (vertices f) ram2 ram1)") apply (simp add: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac zs) apply simp apply (subgoal_tac "ram2 # ys = as") apply force
       apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
      apply simp
      apply (subgoal_tac "ram2 # ys = as") apply (simp add: Edges_def is_sublist_def)
       apply (subgoal_tac "(ram2 # ys) @ c # a # list @ ram1 # vs = as @ c # d # bs")
        apply (thin_tac "ram2 # ys @ c # a # list @ ram1 # vs = as @ c # d # bs")
        apply (rule conjI) apply (rule impI) apply (rule disjI2)+ apply force
        apply (rule impI) apply (rule disjI2)+ apply force
       apply force
      apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
     apply (subgoal_tac "distinct (vertices f21)")
     apply (thin_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # vs = as @ c # d # bs") apply simp
     apply (rule dist_f21)
      (* c \<notin>  set (between (vertices f) ram2 ram1) *)
    apply (subgoal_tac "c = ram2") apply simp
     apply (subgoal_tac "[] = as") apply simp apply (case_tac "between (vertices f) ram2 ram1") apply simp apply simp
     apply (rule dist_at1) apply (rule dist_f21) apply (rule sym)  apply simp apply simp

    (* c \<noteq> ram2 *)
    apply (subgoal_tac "c \<in> set (ram2 # between (vertices f) ram2 ram1 @ ram1 # vs)")
     apply (thin_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # vs = as @ c # d # bs") apply simp
    by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f21 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    apply (case_tac "c = ram2 \<and> d = hd (between (vertices f) ram2 ram1)") apply simp apply (rule disjI1)
     apply (intro exI) apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # vs =
       [] @ ram2 # hd (between (vertices f) ram2 ram1) # tl (between (vertices f) ram2 ram1) @ ram1 # vs") apply assumption apply simp
    apply (case_tac "c = ram1 \<and> d = hd vs") apply (rule disjI1)
     apply (case_tac "vs")  apply simp
     apply simp apply (intro exI)
     apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # a # list =
        (ram2 # between (vertices f) ram2 ram1) @ ram1 # a # list") apply assumption apply simp
    apply (case_tac "c = last vs \<and> d = ram2")
     apply (case_tac vs rule:rev_exhaust) apply simp
     apply simp
    apply simp
    apply (case_tac "c = last (between (vertices f) ram2 ram1) \<and> d = ram1") apply (rule disjI1)
     apply (case_tac "between (vertices f) ram2 ram1" rule: rev_exhaust) apply simp
     apply (intro exI) apply simp
     apply (subgoal_tac "ram2 # ys @ y # ram1 # vs = (ram2 # ys) @ y # ram1 # vs")
      apply assumption
     apply simp
    apply simp
    apply (case_tac "(c, d) \<in> Edges vs") apply (simp add: Edges_def is_sublist_def)
     apply (elim exE) apply simp apply (rule conjI) apply (rule impI) apply (rule disjI1) apply (intro exI)
      apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # as @ [c, d]
        = (ram2 # between (vertices f) ram2 ram1 @ ram1 # as) @ c # d # []") apply assumption apply simp
     apply (rule impI) apply (rule disjI1) apply (intro exI)
     apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ ram1 # as @ c # d # bs
        = (ram2 # between (vertices f) ram2 ram1 @ ram1 # as) @ c # d # bs") apply assumption apply simp
    apply (simp add: Edges_def is_sublist_def)
    apply (elim exE) apply simp apply (rule disjI1) apply (intro exI)
    apply (subgoal_tac "ram2 # as @ c # d # bs @ ram1 # vs = (ram2 # as) @ c # d # (bs @ ram1 # vs)")
     apply assumption by simp
qed


lemma split_face_edges_f21_vs:
assumes vors: "pre_split_face f ram1 ram2 []"
              "(f12, f21) = split_face f ram1 ram2 []"
              "vs2 = between (vertices f) ram2 ram1" "vs2 \<noteq> []"
shows "edges f21 = {(last vs2, ram1) , (ram1, ram2), (ram2, hd vs2)} \<union>
                   Edges vs2" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f21)
    apply (case_tac " c = ram1 \<and> d = ram2") apply simp apply simp  apply (elim exE)

    apply (case_tac "c = ram1") apply simp
    apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 = as")
    apply (subgoal_tac "(ram2 # between (vertices f) ram2 ram1) @ [ram1]  = as @ ram1 # d # bs")
    apply (thin_tac "ram2 # between (vertices f) ram2 ram1 @ [ram1]  = as @ ram1 # d # bs")
    apply simp apply force
    apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
    (* a \<noteq> ram1 *)
    apply (case_tac "c \<in> set (between (vertices f) ram2 ram1)")
    apply (subgoal_tac "distinct (between (vertices f) ram2 ram1)") apply (simp add: in_set_conv_decomp) apply (elim exE) apply simp
    apply (case_tac zs) apply simp apply (subgoal_tac "ram2 # ys = as") apply force
    apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp apply simp
    apply (subgoal_tac "ram2 # ys = as") apply (simp add: Edges_def is_sublist_def)
    apply (subgoal_tac "(ram2 # ys) @ c # a # list @ [ram1] = as @ c # d # bs")
    apply (thin_tac "ram2 # ys @ c # a # list @ [ram1] = as @ c # d # bs")
    apply (rule conjI) apply (rule impI) apply (rule disjI2)+ apply force
    apply (rule impI) apply (rule disjI2)+ apply force apply force
    apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
    apply (subgoal_tac "distinct (vertices f21)")
    apply (thin_tac "ram2 # between (vertices f) ram2 ram1 @ [ram1] = as @ c # d # bs") apply simp
    apply (rule dist_f21)
      (* c \<notin>  set (between (vertices f) ram2 ram1) *)
    apply (subgoal_tac "c = ram2") apply simp
    apply (subgoal_tac "[] = as") apply simp apply (case_tac "between (vertices f) ram2 ram1") apply simp apply simp
    apply (rule dist_at1) apply (rule dist_f21) apply (rule sym)  apply simp apply simp

    (* c \<noteq> ram2 *)
    apply (subgoal_tac "c \<in> set (ram2 # between (vertices f) ram2 ram1 @ [ram1])")
    apply (thin_tac "ram2 # between (vertices f) ram2 ram1 @ [ram1] = as @ c # d # bs") apply simp
    by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f21 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    apply (case_tac "c = ram2 \<and> d = hd (between (vertices f) ram2 ram1)") apply simp apply (rule disjI1)
    apply (intro exI) apply (subgoal_tac "ram2 # between (vertices f) ram2 ram1 @ [ram1] =
       [] @ ram2 # hd (between (vertices f) ram2 ram1) # tl (between (vertices f) ram2 ram1) @ [ram1]") apply assumption apply simp
    apply (case_tac "c = ram1 \<and> d = ram2") apply (rule disjI2) apply simp apply simp
    apply (case_tac "c = last (between (vertices f) ram2 ram1) \<and> d = ram1") apply (rule disjI1)
      apply (case_tac "between (vertices f) ram2 ram1" rule: rev_exhaust) apply simp
      apply (intro exI) apply simp
      apply (subgoal_tac "ram2 # ys @ y # [ram1] = (ram2 # ys) @ y # [ram1]")
      apply assumption apply simp apply simp
    apply (simp add: Edges_def is_sublist_def)
      apply (elim exE) apply simp apply (rule disjI1) apply (intro exI)
      apply (subgoal_tac "ram2 # as @ c # d # bs @ [ram1] = (ram2 # as) @ c # d # (bs @ [ram1])")
      apply assumption by simp
qed


lemma split_face_edges_f21_bet:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "(f12, f21) = split_face f ram1 ram2 vs"
              "vs \<noteq> []" "between (vertices f) ram2 ram1 = []"
shows "edges f21 = {(ram1, hd vs), (last vs, ram2), (ram2, ram1)} \<union>
                   Edges vs" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f21)
    apply (case_tac " c = last vs \<and> d = ram2") apply simp
    apply simp apply (elim exE)
    apply (case_tac "c = ram1") apply simp
     apply (subgoal_tac "[ram2] = as") apply clarsimp
     apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
    (* a \<noteq> ram1 *)
    apply (case_tac "c \<in> set vs")
     apply (subgoal_tac "distinct vs") apply (simp add: in_set_conv_decomp) apply (elim exE) apply simp
      apply (case_tac "zs") apply simp
       apply (subgoal_tac "ram2 #  ram1 # ys = as") apply force
       apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
      apply simp
      apply (subgoal_tac "ram2 # ram1 # ys = as")
       apply (subgoal_tac "(ram2 # ram1 # ys) @ c # a # list = as @ c # d # bs")
        apply (thin_tac "ram2 #  ram1 # ys @ c # a # list = as @ c # d # bs")
        apply (simp add: Edges_def is_sublist_def) apply force
       apply force
      apply (rule dist_at1) apply (rule dist_f21) apply (rule sym) apply simp apply simp
     apply (simp add: pre_split_face_def)
    (* c \<notin> set (rev vs) *)
    apply (subgoal_tac "c = ram2") apply simp
     apply (subgoal_tac "[] = as") apply simp
     apply (rule dist_at1) apply (rule dist_f21) apply (rule sym)  apply simp apply simp
    (* c \<noteq> ram2 *)
    apply (subgoal_tac "c \<in> set (ram2 # ram1 # vs)")
     apply (thin_tac "ram2 # ram1 # vs = as @ c # d # bs") apply simp
    by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f21 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    apply (case_tac "c = ram2 \<and> d = ram1") apply simp apply (rule disjI1) apply force
    apply (case_tac "c = ram1 \<and> d = hd vs") apply (rule disjI1)
     apply (case_tac "vs")  apply simp
     apply simp apply (intro exI)
     apply (subgoal_tac "ram2 # ram1 # a # list =
        [ram2] @ ram1 # a # list") apply assumption  apply simp
    apply (case_tac "c = last vs \<and> d = ram2")
     apply (case_tac vs rule: rev_exhaust) apply simp
     apply simp
    apply (simp add: Edges_def is_sublist_def)
    apply (elim exE) apply simp apply (rule conjI) apply (rule impI) apply (rule disjI1) apply (intro exI)
     apply (subgoal_tac "ram2 # ram1 # as @ [c, d]
        = (ram2 # ram1 # as) @ c # d # []") apply assumption apply simp
    apply (rule impI) apply (rule disjI1) apply (intro exI)
    apply (subgoal_tac "ram2 #  ram1 # as @ c # d # bs
        = (ram2 # ram1 # as) @ c # d # bs") apply assumption by simp
qed


lemma split_face_edges_f21_bet_vs:
assumes vors: "pre_split_face f ram1 ram2 []"
              "(f12, f21) = split_face f ram1 ram2 []"
              "between (vertices f) ram2 ram1 = []"
shows "edges f21 = {(ram1, ram2), (ram2, ram1)}" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?rhs"
    apply (simp add: split_face_def is_nextElem_def is_sublist_def dist_f21)
    apply (case_tac " c = ram1 \<and> d = ram2") apply simp  apply simp apply (elim exE)
    apply (case_tac "as") apply  simp  apply (case_tac "list") by auto
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f21: "distinct (vertices f21)" apply (rule_tac split_face_distinct2) by auto
  from x vors show "x \<in> ?lhs"
    apply (simp add: dist_f21 is_nextElem_def is_sublist_def) apply (simp add: split_face_def)
    by auto
qed

lemma split_face_edges_f21_subset: "pre_split_face f ram1 ram2 vs \<Longrightarrow>
  (f12, f21) = split_face f ram1 ram2 vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow>
  {(last vs, ram2), (ram1, hd vs)} \<union> Edges vs \<subseteq> edges f21"
  apply (case_tac "between (vertices f) ram2 ram1")
    apply (frule split_face_edges_f21_bet)  apply simp apply simp apply simp apply force
    apply (frule split_face_edges_f21) apply simp+ by force

lemma verticesFrom_ram1: "pre_split_face f ram1 ram2 vs \<Longrightarrow>
  verticesFrom f ram1 = ram1 # between (vertices f) ram1 ram2 @ ram2 # between (vertices f) ram2 ram1"
  apply (subgoal_tac "pre_between (vertices f) ram1 ram2")
  apply (subgoal_tac "distinct (vertices f)")
  apply (case_tac "before (vertices f) ram1 ram2")
  apply (simp add: verticesFrom_Def)
  apply (subgoal_tac "ram2 \<in> set (snd (splitAt ram1 (vertices f)))") apply (drule splitAt_ram)
  apply (subgoal_tac "snd (splitAt ram2 (snd (splitAt ram1 (vertices f)))) = snd (splitAt ram2 (vertices f))")
  apply simp apply (thin_tac "snd (splitAt ram1 (vertices f)) =
     fst (splitAt ram2 (snd (splitAt ram1 (vertices f)))) @
     ram2 # snd (splitAt ram2 (snd (splitAt ram1 (vertices f))))")  apply simp
  apply (rule before_dist_r2) apply simp apply simp
  apply (subgoal_tac "before (vertices f) ram2 ram1")
  apply (subgoal_tac "pre_between (vertices f) ram2 ram1")
  apply (simp add: verticesFrom_Def)
  apply (subgoal_tac "ram2 \<in> set (fst (splitAt ram1 (vertices f)))") apply (drule splitAt_ram)
  apply (subgoal_tac "fst (splitAt ram2 (fst (splitAt ram1 (vertices f)))) = fst (splitAt ram2 (vertices f))")
  apply simp apply (thin_tac "fst (splitAt ram1 (vertices f)) =
     fst (splitAt ram2 (fst (splitAt ram1 (vertices f)))) @
     ram2 # snd (splitAt ram2 (fst (splitAt ram1 (vertices f))))") apply simp
  apply (rule before_dist_r1) apply simp apply simp apply (simp add: pre_between_def) apply force
  apply (simp add: pre_split_face_def) by (rule pre_split_face_p_between)

lemma split_face_edges_f_vs1_vs2:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "between (vertices f) ram1 ram2 = []"
              "between (vertices f) ram2 ram1 = []"
shows "edges f = {(ram2, ram1) , (ram1, ram2)}" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?rhs" apply (simp add: dist_f)
    apply (subgoal_tac "pre_between (vertices f) ram1 ram2")
     apply (drule is_nextElem_or) apply assumption
     apply (simp add: Edges_def)
     apply (case_tac "is_sublist [c, d] [ram1, ram2]") apply (simp)
     apply (simp) apply blast
    by (rule pre_split_face_p_between)
  next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?lhs" apply (simp add: dist_f)
    apply (subgoal_tac "ram1 \<in> \<V> f") apply (simp add: verticesFrom_is_nextElem verticesFrom_ram1)
    apply (simp add: is_nextElem_def) apply blast
    by (simp add: pre_split_face_def)
qed

lemma split_face_edges_f_vs1:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "between (vertices f) ram1 ram2 = []"
              "vs2 = between (vertices f) ram2 ram1" "vs2 \<noteq> []"
shows "edges f = {(last vs2, ram1) , (ram1, ram2), (ram2, hd vs2)} \<union>
                 Edges vs2" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from vors have dist_vs2: "distinct (ram2 # vs2 @ [ram1])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) apply (rule not_sym) by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?rhs" apply (simp add: dist_f)
    apply (subgoal_tac "pre_between (vertices f) ram1 ram2")
     apply (drule is_nextElem_or) apply assumption
     apply (simp add: Edges_def)
     apply (case_tac "is_sublist [c, d] [ram1, ram2]")
      apply simp
     apply simp
     apply(erule disjE) apply blast
     apply (case_tac "c = ram2")
      apply (case_tac "between (vertices f) ram2 ram1") apply simp
      apply simp
      apply (drule is_sublist_distinct_prefix)
       apply (subgoal_tac "distinct (ram2 # vs2 @ [ram1])")
        apply simp
       apply (rule dist_vs2)
      apply simp
     apply (case_tac "c = ram1")
      apply (subgoal_tac "\<not> is_sublist [c, d] (ram2 # vs2 @ [ram1])")
       apply simp
      apply (rule is_sublist_notlast)
       apply (rule_tac dist_vs2)
      apply simp
     apply simp
     apply (simp add: is_sublist_def)
     apply (elim exE)
     apply (case_tac "between (vertices f) ram2 ram1" rule: rev_exhaust) apply simp
     apply simp
     apply (case_tac "bs" rule: rev_exhaust) apply simp
     apply simp
     apply (rule disjI2)
     apply (intro exI)
     apply simp
    apply (rule pre_split_face_p_between) by simp
  next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from vors have dist_vs2: "distinct (ram2 # vs2 @ [ram1])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) apply (rule not_sym) by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?lhs" apply (simp add: dist_f)
    apply (subgoal_tac "ram1 \<in> set (vertices f)") apply (simp add: verticesFrom_is_nextElem verticesFrom_ram1)
    apply (simp add: is_nextElem_def)
    apply (case_tac "c = last (between (vertices f) ram2 ram1) \<and> d = ram1") apply simp apply simp apply (rule disjI1)
    apply (case_tac "c = ram1 \<and> d = ram2")  apply (simp add: is_sublist_def) apply force apply simp
    apply (case_tac "c = ram2 \<and> d = hd (between (vertices f) ram2 ram1)")
      apply (case_tac "between (vertices f) ram2 ram1") apply simp apply (simp add: is_sublist_def) apply (intro exI)
      apply (subgoal_tac "ram1 # ram2 # a # list =
        [ram1] @ ram2 # a # (list)") apply assumption apply simp
    apply simp
      apply (subgoal_tac "is_sublist [c, d] ((ram1 #
                        [ram2]) @ between (vertices f) ram2 ram1 @ [])")
      apply simp apply (rule is_sublist_add) apply (simp add: Edges_def)
    by (simp add: pre_split_face_def)
qed


lemma split_face_edges_f_vs2:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "vs1 = between (vertices f) ram1 ram2" "vs1 \<noteq> []"
              "between (vertices f) ram2 ram1 = []"
shows "edges f = {(ram2, ram1) , (ram1, hd vs1), (last vs1, ram2)} \<union>
                 Edges vs1" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from vors have dist_vs1: "distinct (ram1 # vs1 @ [ram2])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?rhs" apply (simp add: dist_f)
    apply (subgoal_tac "pre_between (vertices f) ram1 ram2")
     apply (drule is_nextElem_or) apply assumption
     apply (simp add: Edges_def)
     apply (case_tac "is_sublist [c, d] (ram1 # between (vertices f) ram1 ram2 @ [ram2])")
      apply simp
      apply (case_tac "c = ram1")
       apply (case_tac "between (vertices f) ram1 ram2") apply simp
       apply simp
       apply (drule is_sublist_distinct_prefix)
        apply (subgoal_tac "distinct (ram1 # vs1 @ [ram2])") apply simp
        apply (rule dist_vs1)
       apply simp
      apply (case_tac "c = ram2")
       apply (subgoal_tac "\<not> is_sublist [c, d] (ram1 # vs1 @ [ram2])") apply simp
       apply (rule is_sublist_notlast) apply (rule_tac dist_vs1)
       apply simp
      apply simp
      apply (simp add: is_sublist_def)
      apply (elim exE)
      apply (case_tac "between (vertices f) ram1 ram2" rule: rev_exhaust) apply simp
      apply simp
      apply (case_tac "bs" rule: rev_exhaust) apply simp
      apply simp
      apply (rule disjI2)
      apply (intro exI)
      apply simp
     apply simp
    apply (rule pre_split_face_p_between) by simp
  next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from vors have dist_vs1: "distinct (ram1 # vs1 @ [ram2])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?lhs" apply (simp add: dist_f)
    apply (subgoal_tac "ram1 \<in> \<V> f") apply (simp add: verticesFrom_is_nextElem verticesFrom_ram1)
    apply (simp add: is_nextElem_def)
    apply (case_tac "c = ram2 \<and> d = ram1") apply simp apply simp apply (rule disjI1)
    apply (case_tac "c = ram1 \<and> d = hd (between (vertices f) ram1 ram2)")
      apply (case_tac "between (vertices f) ram1 ram2") apply simp apply (force simp: is_sublist_def) apply simp
    apply (case_tac "c = last (between (vertices f) ram1 ram2) \<and> d = ram2")
      apply (case_tac "between (vertices f) ram1 ram2" rule: rev_exhaust) apply simp apply (simp add: is_sublist_def)
      apply (intro exI)
      apply (subgoal_tac "ram1 # ys @ [y, ram2] =
        (ram1 # ys) @ y # ram2 # []") apply assumption apply simp
    apply simp
      apply (simp add: Edges_def)
      apply (subgoal_tac "is_sublist [c, d] ([ram1] @ between (vertices f) ram1 ram2 @ [ram2])")
      apply simp apply (rule is_sublist_add) apply simp
    by (simp add: pre_split_face_def)
qed


lemma split_face_edges_f:
assumes vors: "pre_split_face f ram1 ram2 vs"
              "vs1 = between (vertices f) ram1 ram2" "vs1 \<noteq> []"
              "vs2 = between (vertices f) ram2 ram1" "vs2 \<noteq> []"
shows "edges f = {(last vs2, ram1) , (ram1, hd vs1), (last vs1, ram2), (ram2, hd vs2)} \<union>
                 Edges vs1 \<union> Edges vs2" (is "?lhs = ?rhs")
proof (intro equalityI subsetI)
  fix x
  assume x: "x \<in> ?lhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from vors have dist_vs1: "distinct (ram1 # vs1 @ [ram2])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) by (simp add: pre_split_face_def)
  from vors have dist_vs2: "distinct (ram2 # vs2 @ [ram1])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) apply (rule not_sym) by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?rhs" apply (simp add: dist_f)
    apply (subgoal_tac "pre_between (vertices f) ram1 ram2")
    apply (drule is_nextElem_or) apply assumption apply (simp add: Edges_def)
    apply (case_tac "is_sublist [c, d] (ram1 # between (vertices f) ram1 ram2 @ [ram2])") apply simp
      apply (case_tac "c = ram1")
        apply (case_tac "between (vertices f) ram1 ram2") apply simp apply simp
        apply (drule is_sublist_distinct_prefix) apply (subgoal_tac "distinct (ram1 # vs1 @ [ram2])")
        apply simp apply (rule dist_vs1) apply simp
      apply (case_tac "c = ram2")
        apply (subgoal_tac "\<not> is_sublist [c, d] (ram1 # vs1 @ [ram2])") apply simp
        apply (rule is_sublist_notlast) apply (rule_tac dist_vs1) apply simp
      apply simp apply (simp add: is_sublist_def) apply (elim exE)
        apply (case_tac "between (vertices f) ram1 ram2" rule: rev_exhaust) apply simp apply simp
        apply (case_tac "bs" rule: rev_exhaust) apply simp apply simp
        apply (rule disjI2) apply (rule disjI2) apply (rule disjI1) apply (intro exI) apply simp
    apply simp
      apply (case_tac "c = ram2")
        apply (case_tac "between (vertices f) ram2 ram1") apply simp apply simp
        apply (drule is_sublist_distinct_prefix) apply (subgoal_tac "distinct (ram2 # vs2 @ [ram1])")
        apply simp apply (rule dist_vs2) apply simp
      apply (case_tac "c = ram1")
        apply (subgoal_tac "\<not> is_sublist [c, d] (ram2 # vs2 @ [ram1])") apply simp
        apply (rule is_sublist_notlast) apply (rule_tac dist_vs2) apply simp
      apply simp apply (simp add: is_sublist_def) apply (elim exE)
        apply (case_tac "between (vertices f) ram2 ram1" rule: rev_exhaust) apply simp apply simp
        apply (case_tac "bs" rule: rev_exhaust) apply simp apply simp
        apply (rule disjI2) apply (rule disjI2) apply (rule disjI2) apply (intro exI) apply simp
   apply (rule pre_split_face_p_between) by simp
next
  fix x
  assume x: "x \<in> ?rhs"
  define c where "c = fst x"
  define d where "d = snd x"
  with c_def  have [simp]: "x = (c,d)" by simp
  from vors have dist_f: "distinct (vertices f)" by (simp add: pre_split_face_def)
  from vors have dist_vs1: "distinct (ram1 # vs1 @ [ram2])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) by (simp add: pre_split_face_def)
  from vors have dist_vs2: "distinct (ram2 # vs2 @ [ram1])" apply (simp only:)
    apply (rule between_distinct_r12) apply (rule dist_f) apply (rule not_sym) by (simp add: pre_split_face_def)
  from x vors show "x \<in> ?lhs" apply (simp add: dist_f)
    apply (subgoal_tac "ram1 \<in> \<V> f") apply (simp add: verticesFrom_is_nextElem verticesFrom_ram1)
    apply (simp add: is_nextElem_def)
    apply (case_tac "c = last (between (vertices f) ram2 ram1) \<and> d = ram1") apply simp apply simp apply (rule disjI1)
    apply (case_tac "c = ram1 \<and> d = hd (between (vertices f) ram1 ram2)")
      apply (case_tac "between (vertices f) ram1 ram2") apply simp apply (force simp: is_sublist_def) apply simp
    apply (case_tac "c = last (between (vertices f) ram1 ram2) \<and> d = ram2")
      apply (case_tac "between (vertices f) ram1 ram2" rule: rev_exhaust) apply simp apply (simp add: is_sublist_def)
      apply (intro exI)
      apply (subgoal_tac "ram1 # ys @ y # ram2 # between (vertices f) ram2 ram1 =
        (ram1 # ys) @ y # ram2 # (between (vertices f) ram2 ram1)") apply assumption apply simp apply simp
    apply (case_tac "c = ram2 \<and> d = hd (between (vertices f) ram2 ram1)")
      apply (case_tac "between (vertices f) ram2 ram1") apply simp apply (simp add: is_sublist_def) apply (intro exI)
      apply (subgoal_tac "ram1 # between (vertices f) ram1 ram2 @ ram2 # a # list =
        (ram1 # between (vertices f) ram1 ram2) @ ram2 # a # (list)") apply assumption apply simp apply simp
    apply (case_tac "(c, d) \<in> Edges (between (vertices f) ram1 ram2)") apply (simp add: Edges_def)
      apply (subgoal_tac "is_sublist [c, d] ([ram1] @ between (vertices f) ram1 ram2 @
                        (ram2 # between (vertices f) ram2 ram1))")
      apply simp apply (rule is_sublist_add) apply simp
    apply simp
      apply (subgoal_tac "is_sublist [c, d] ((ram1 # between (vertices f) ram1 ram2 @
                        [ram2]) @ between (vertices f) ram2 ram1 @ [])")
      apply simp apply (rule is_sublist_add) apply (simp add: Edges_def)
    by (simp add: pre_split_face_def)
qed


lemma split_face_edges_f12_f21:
  "pre_split_face f ram1 ram2 vs \<Longrightarrow> (f12, f21) = split_face f ram1 ram2 vs \<Longrightarrow>
   vs \<noteq> []
  \<Longrightarrow> edges f12 \<union> edges f21 = edges f \<union>
     {(hd vs, ram1), (ram1, hd vs), (last vs, ram2), (ram2, last vs)} \<union>
     Edges vs \<union>
     Edges (rev vs)"
  apply (case_tac "between (vertices f) ram1 ram2 = []")
    apply (case_tac "between (vertices f) ram2 ram1 = []")
      apply (simp add: split_face_edges_f12_bet split_face_edges_f21_bet split_face_edges_f_vs1_vs2)
      apply force
    apply (simp add: split_face_edges_f12_bet split_face_edges_f21 split_face_edges_f_vs1) apply force
  apply (case_tac "between (vertices f) ram2 ram1 = []")
    apply (simp add: split_face_edges_f21_bet split_face_edges_f12 split_face_edges_f_vs2) apply force
  apply (simp add: split_face_edges_f21 split_face_edges_f12 split_face_edges_f) by force


lemma split_face_edges_f12_f21_vs:
  "pre_split_face f ram1 ram2 [] \<Longrightarrow> (f12, f21) = split_face f ram1 ram2 []
  \<Longrightarrow> edges f12 \<union> edges f21 = edges f \<union>
     {(ram2, ram1), (ram1, ram2)}"
  apply (case_tac "between (vertices f) ram1 ram2 = []")
    apply (case_tac "between (vertices f) ram2 ram1 = []")
      apply (simp add: split_face_edges_f12_bet_vs split_face_edges_f21_bet_vs split_face_edges_f_vs1_vs2)
      apply force
    apply (simp add: split_face_edges_f12_bet_vs split_face_edges_f21_vs split_face_edges_f_vs1) apply force
  apply (case_tac "between (vertices f) ram2 ram1 = []")
    apply (simp add: split_face_edges_f21_bet_vs split_face_edges_f12_vs split_face_edges_f_vs2) apply force
  apply (simp add: split_face_edges_f21_vs split_face_edges_f12_vs split_face_edges_f) by force


lemma split_face_edges_f12_f21_sym:
  "f \<in> \<F> g \<Longrightarrow>
  pre_split_face f ram1 ram2 vs \<Longrightarrow> (f12, f21) = split_face f ram1 ram2 vs
  \<Longrightarrow> ((a,b) \<in> edges f12 \<or> (a,b) \<in>  edges f21) =
     ((a,b) \<in> edges f  \<or>
  (((b,a) \<in> edges f12 \<or> (b,a) \<in>  edges f21) \<and>
  ((a,b) \<in> edges f12 \<or> (a,b) \<in> edges f21)))"
  apply (subgoal_tac "((a,b) \<in> edges f12 \<union> edges f21) =
     ((a,b) \<in> edges f \<or> ((b,a) \<in> edges f12 \<union> edges f21) \<and> (a,b) \<in> edges f12 \<union> edges f21)") apply force
  apply (case_tac "vs = []")
    apply (subgoal_tac "pre_split_face f ram1 ram2 []")
    apply (drule split_face_edges_f12_f21_vs) apply simp apply simp apply force apply simp
  apply (drule split_face_edges_f12_f21) apply simp apply simp
    apply simp by force

lemma splitFace_edges_g'_help: "pre_splitFace g ram1 ram2 f vs \<Longrightarrow>
  (f12, f21, g') = splitFace g ram1 ram2 f vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow>
  edges g' = edges g \<union> edges f \<union> Edges vs \<union> Edges(rev vs) \<union>
  {(ram2, last vs), (hd vs, ram1), (ram1, hd vs), (last vs, ram2)}"
proof -
  assume pre: "pre_splitFace g ram1 ram2 f vs"
    and fdg: "(f12, f21, g') = splitFace g ram1 ram2 f vs"
    and vs_neq: "vs \<noteq> []"

  from pre fdg have split: "(f12, f21) = split_face f ram1 ram2 vs"
    apply (unfold pre_splitFace_def) apply (elim conjE)
    by (simp add: splitFace_split_face)

  from fdg pre have "edges g' = (\<Union>\<^bsub>a\<in>set (replace f [f21] (faces g))\<^esub> edges a) \<union>
       edges (f12)" by(auto simp: splitFace_def split_def edges_graph_def)
  with pre vs_neq show ?thesis apply (simp add: UNION_eq) apply (rule equalityI) apply simp
    apply (rule conjI) apply (rule subsetI) apply simp apply (erule bexE) apply (drule replace5)
    apply (case_tac "xa \<in> \<F> g") apply simp
    apply (subgoal_tac "x \<in> edges g") apply simp
    apply (simp add: edges_graph_def) apply force
    apply simp
    apply (subgoal_tac "pre_split_face f ram1 ram2 vs")
    apply (case_tac "between (vertices f) ram2 ram1 = []")
      apply (frule split_face_edges_f21_bet) apply (rule split) apply simp apply simp
      apply (case_tac "between (vertices f) ram1 ram2 = []")
        apply (frule split_face_edges_f_vs1_vs2) apply simp apply simp apply simp apply force
        apply (frule split_face_edges_f_vs2) apply simp apply simp apply simp apply force
    apply (frule split_face_edges_f21) apply (rule split) apply simp apply simp apply simp
      apply (case_tac "between (vertices f) ram1 ram2 = []")
        apply (frule split_face_edges_f_vs1) apply simp apply simp apply simp apply simp apply force
        apply (frule split_face_edges_f) apply simp apply simp apply simp apply simp apply force
    apply simp
    apply (subgoal_tac "pre_split_face f ram1 ram2 vs")
    apply (case_tac "between (vertices f) ram1 ram2 = []")
      apply (frule split_face_edges_f12_bet) apply (rule split) apply simp apply simp
      apply (case_tac "between (vertices f) ram2 ram1 = []")
        apply (frule split_face_edges_f_vs1_vs2) apply simp apply simp apply simp apply force
        apply (frule split_face_edges_f_vs1) apply simp apply simp apply simp apply force
    apply (frule split_face_edges_f12) apply (rule split) apply simp apply simp apply simp
      apply (case_tac "between (vertices f) ram2 ram1 = []")
        apply (frule split_face_edges_f_vs2) apply simp apply simp apply simp apply simp apply force
        apply (frule split_face_edges_f) apply simp apply simp apply simp apply simp apply force
    apply simp
    apply simp
    apply (subgoal_tac "pre_split_face f ram1 ram2 vs")
    apply (subgoal_tac "(ram2, last vs) \<in> edges f12 \<and> (hd vs, ram1) \<in> edges f12")
      apply (rule conjI) apply simp
      apply (rule conjI) apply simp
    apply (subgoal_tac "(ram1, hd vs) \<in> edges f21 \<and> (last vs, ram2) \<in> edges f21")
      apply (rule conjI) apply (rule disjI1) apply (rule bexI) apply (elim conjE) apply simp
        apply (rule replace3) apply(erule pre_splitFace_oldF) apply simp
      apply (rule conjI) apply (rule disjI1) apply (rule bexI) apply (elim conjE) apply simp
        apply (rule replace3) apply(erule pre_splitFace_oldF)
    apply simp
    apply (subgoal_tac "edges f \<subseteq> {y. \<exists>x\<in>set (replace f [f21] (faces g)). y \<in> edges x} \<union> edges f12")
    apply (subgoal_tac "edges g \<subseteq> {y. \<exists>x\<in>set (replace f [f21] (faces g)). y \<in> edges x} \<union> edges f12")
      apply (rule conjI) apply simp
      apply (rule conjI) apply simp
    apply (subgoal_tac "Edges(rev vs) \<subseteq> edges f12") apply (rule conjI) prefer 2 apply blast
    apply (subgoal_tac "Edges vs \<subseteq> edges f21")
      apply (subgoal_tac "Edges vs \<subseteq> {y. \<exists>x\<in>set (replace f [f21] (faces g)). y \<in> edges x}") apply blast
      apply (rule subset_trans) apply  assumption apply (rule subsetI) apply simp apply (rule bexI) apply simp
      apply (rule replace3) apply(erule pre_splitFace_oldF) apply simp
    (* jetzt alle 7 subgoals aufloesen *)
    apply (frule split_face_edges_f21_subset) apply (rule split)  apply simp apply simp
    apply (frule split_face_edges_f12_subset) apply (rule split) apply simp apply simp
    apply (simp add: edges_graph_def)  apply (rule subsetI) apply simp apply (elim bexE)
      apply (case_tac "xa = f") apply simp apply blast
      apply (rule disjI1) apply (rule bexI) apply simp apply (rule replace4) apply simp apply force
    apply (rule subsetI)
      apply (subgoal_tac "\<exists> u v. x = (u,v)") apply (elim exE conjE)
      apply (frule split_face_edges_or [OF split]) apply simp
      apply (case_tac "(u, v) \<in> edges f12") apply simp apply simp
      apply (rule bexI) apply (thin_tac "(u, v) \<in> edges f")  apply assumption
      apply (rule replace3) apply(erule pre_splitFace_oldF) apply simp apply simp
    apply (frule split_face_edges_f21_subset) apply (rule split) apply simp apply simp
    apply (frule split_face_edges_f12_subset) apply (rule split) apply simp apply simp
  by simp
qed

lemma pre_splitFace_edges_f_in_g: "pre_splitFace g ram1 ram2 f vs \<Longrightarrow> edges f \<subseteq> edges g"
  apply (simp add: edges_graph_def) by (force)

lemma pre_splitFace_edges_f_in_g2: "pre_splitFace g ram1 ram2 f vs \<Longrightarrow> x \<in> edges f \<Longrightarrow> x \<in> edges g"
  apply (simp add: edges_graph_def) by (force)

lemma splitFace_edges_g': "pre_splitFace g ram1 ram2 f vs \<Longrightarrow>
  (f12, f21, g') = splitFace g ram1 ram2 f vs \<Longrightarrow> vs \<noteq> [] \<Longrightarrow>
  edges g' = edges g \<union> Edges vs \<union> Edges(rev vs) \<union>
  {(ram2, last vs), (hd vs, ram1), (ram1, hd vs), (last vs, ram2)}"
  apply (subgoal_tac "edges g \<union> edges f = edges g")
  apply (frule splitFace_edges_g'_help) apply simp apply simp apply simp
  apply (frule pre_splitFace_edges_f_in_g) by blast


lemma splitFace_edges_g'_vs: "pre_splitFace g ram1 ram2 f [] \<Longrightarrow>
  (f12, f21, g') = splitFace g ram1 ram2 f []  \<Longrightarrow>
  edges g' = edges g \<union> {(ram1, ram2), (ram2, ram1)}"
proof -
  assume pre: "pre_splitFace g ram1 ram2 f []"
    and fdg: "(f12, f21, g') = splitFace g ram1 ram2 f []"

  from pre fdg have split: "(f12, f21) = split_face f ram1 ram2 []"
    apply (unfold pre_splitFace_def) apply (elim conjE)
    by (simp add: splitFace_split_face)

  from fdg pre have "edges g' = (\<Union>\<^bsub>a\<in>set (replace f [f21] (faces g))\<^esub> edges a) \<union>
       edges (f12)" by (auto simp: splitFace_def split_def edges_graph_def)
  with pre show ?thesis apply (simp add: UNION_eq) apply (rule equalityI) apply simp
    apply (rule conjI) apply (rule subsetI) apply simp apply (erule bexE) apply (drule replace5)
    apply (case_tac "xa \<in> \<F> g") apply simp
    apply (subgoal_tac "x \<in> edges g") apply simp
    apply (simp add: edges_graph_def) apply force
    apply simp
    apply (subgoal_tac "pre_split_face f ram1 ram2 []")
    apply (case_tac "between (vertices f) ram2 ram1 = []") apply (simp add: pre_FaceDiv_between2)
      apply (frule split_face_edges_f21_vs) apply (rule split) apply simp apply simp apply simp
      apply (case_tac "x = (ram1, ram2)") apply simp apply simp apply (rule disjI2)
      apply (rule pre_splitFace_edges_f_in_g2)  apply simp
      apply (subgoal_tac "pre_split_face f ram1 ram2 []")
      apply (frule split_face_edges_f) apply simp apply simp apply (rule pre_FaceDiv_between1) apply simp apply simp
      apply simp apply force  apply simp apply simp

    apply (rule subsetI) apply simp
    apply (subgoal_tac "pre_split_face f ram1 ram2 []")
    apply (case_tac "between (vertices f) ram1 ram2 = []") apply (simp add: pre_FaceDiv_between1)
      apply (frule split_face_edges_f12_vs) apply (rule split) apply simp apply simp apply simp
      apply (case_tac "x = (ram2, ram1)") apply simp apply simp apply (rule disjI2)
      apply (rule pre_splitFace_edges_f_in_g2)  apply simp
      apply (subgoal_tac "pre_split_face f ram1 ram2 []")
      apply (frule split_face_edges_f) apply simp apply simp apply simp apply (rule pre_FaceDiv_between2) apply simp
      apply simp apply force apply simp apply simp
   apply simp
   apply (subgoal_tac "pre_split_face f ram1 ram2 []")
   apply (subgoal_tac "(ram1, ram2) \<in> edges f21")
   apply (rule conjI) apply (rule disjI1) apply (rule bexI) apply simp apply (force)
   apply (subgoal_tac "(ram2, ram1) \<in> edges f12")
   apply (rule conjI) apply force
   apply (rule subsetI) apply (simp add: edges_graph_def) apply (elim bexE)
     apply (case_tac "xa = f") apply simp
     apply (subgoal_tac "\<exists> u v. x = (u,v)") apply (elim exE conjE)
     apply (subgoal_tac "pre_split_face f ram1 ram2 []")
     apply (frule split_face_edges_or [OF split]) apply simp
     apply (case_tac "(u, v) \<in> edges f12") apply simp apply simp apply force apply simp  apply simp
     apply (rule disjI1) apply (rule bexI) apply simp apply (rule replace4) apply simp apply force
   apply (frule split_face_edges_f12_vs) apply simp apply (rule split) apply simp
     apply (rule pre_FaceDiv_between1) apply simp apply simp
   apply (frule split_face_edges_f21_vs) apply simp apply (rule split) apply simp
     apply (rule pre_FaceDiv_between2) apply simp apply simp
   by simp
qed


lemma splitFace_edges_incr:
 "pre_splitFace g ram1 ram2 f vs \<Longrightarrow>
  (f\<^sub>1, f\<^sub>2, g') = splitFace g ram1 ram2 f vs  \<Longrightarrow>
  edges g \<subseteq> edges g'"
apply(cases vs)
 apply(simp add:splitFace_edges_g'_vs)
 apply blast
apply(simp add:splitFace_edges_g')
apply blast
done

lemma snd_snd_splitFace_edges_incr:
 "pre_splitFace g v\<^sub>1 v\<^sub>2 f vs \<Longrightarrow>
  edges g \<subseteq> edges(snd(snd(splitFace g v\<^sub>1 v\<^sub>2 f vs)))"
apply(erule splitFace_edges_incr
 [where f\<^sub>1 = "fst(splitFace g v\<^sub>1 v\<^sub>2 f vs)"
  and f\<^sub>2 = "fst(snd(splitFace g v\<^sub>1 v\<^sub>2 f vs))"])
apply(auto)
done


(********************* Vorbereitung für subdivFace *****************)

(**** computes the list of ram vertices **********)
subsection \<open>\<open>removeNones\<close>\<close>

definition removeNones :: "'a option list \<Rightarrow> 'a list" where
"removeNones vOptionList \<equiv> [the x. x \<leftarrow> vOptionList, x \<noteq> None]"

(* "removeNones vOptionList \<equiv> map the [x \<in> vOptionList. x \<noteq> None]" *)

declare  removeNones_def [simp]
lemma removeNones_inI[intro]: "Some a \<in> set ls \<Longrightarrow> a \<in> set (removeNones ls)" by (induct ls)  auto
lemma removeNones_hd[simp]: "removeNones ( Some a # ls) = a # removeNones ls" by auto
lemma removeNones_last[simp]: "removeNones (ls @ [Some a]) = removeNones ls @ [a]" by auto
lemma removeNones_in[simp]: "removeNones (as @ Some a # bs) = removeNones as @ a # removeNones bs" by auto
lemma removeNones_none_hd[simp]: "removeNones ( None # ls) = removeNones ls" by auto
lemma removeNones_none_last[simp]: "removeNones (ls @ [None]) = removeNones ls" by auto
lemma removeNones_none_in[simp]: "removeNones (as @ None # bs) = removeNones (as @ bs)" by auto
lemma removeNones_empty[simp]: "removeNones [] = []" by auto
declare removeNones_def [simp del]





(************* natToVertexList ************)
subsection\<open>\<open>natToVertexList\<close>\<close>

(* Hilfskonstrukt natToVertexList *)
primrec natToVertexListRec ::
  "nat \<Rightarrow> vertex \<Rightarrow> face \<Rightarrow> nat list \<Rightarrow> vertex option list"
where
  "natToVertexListRec old v f [] = []" |
  "natToVertexListRec old v f (i#is) =
    (if i = old then None#natToVertexListRec i v f is
     else Some (f\<^bsup>i\<^esup> \<bullet> v)
          # natToVertexListRec i v f is)"

primrec natToVertexList ::
  "vertex \<Rightarrow> face \<Rightarrow> nat list \<Rightarrow> vertex option list"
where
  "natToVertexList v f [] = []" |
  "natToVertexList v f (i#is) =
    (if i = 0 then (Some v)#(natToVertexListRec i v f is) else [])"


subsection \<open>@{const indexToVertexList}\<close>

lemma  nextVertex_inj:
 "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow>
 i < length (vertices (f::face)) \<Longrightarrow> a < length (vertices f) \<Longrightarrow>
 f\<^bsup>a\<^esup>\<bullet>v = f\<^bsup>i\<^esup>\<bullet>v \<Longrightarrow> i = a"
proof -
  assume d: "distinct (vertices f)" and v: "v \<in> \<V> f" and i: "i < length (vertices (f::face))"
    and a: "a < length (vertices f)" and eq:" f\<^bsup>a\<^esup>\<bullet>v = f\<^bsup>i\<^esup>\<bullet>v"
  then have eq: "(verticesFrom f v)!a = (verticesFrom f v)!i " by (simp add: verticesFrom_nth)
  define xs where "xs = verticesFrom f v"
  with eq have eq: "xs!a = xs!i" by auto
  from d v have z: "distinct (verticesFrom f v)" by auto
  moreover
  from xs_def a v d have "(verticesFrom f v) = take a xs @ xs ! a # drop (Suc a) xs"
    by (auto intro: id_take_nth_drop simp: verticesFrom_length)
  with eq have "(verticesFrom f v) = take a xs @ xs ! i # drop (Suc a) xs" by simp
  moreover
  from xs_def i v d have "(verticesFrom f v) = take i xs @ xs ! i # drop (Suc i) xs"
    by (auto intro: id_take_nth_drop simp: verticesFrom_length)
  ultimately have "take a xs = take i xs" by (rule dist_at1)
  moreover
  from v d have vertFrom[simp]: "length (vertices f) = length (verticesFrom f v)"
    by (auto simp: verticesFrom_length)
  from xs_def a i have "a < length xs" "i < length xs" by auto
  moreover
  have "\<And> a i. a < length xs \<Longrightarrow> i < length xs \<Longrightarrow> take a xs = take i xs \<Longrightarrow> a = i"
  proof (induct xs)
    case Nil then show ?case by auto
  next
    case (Cons x xs) then show ?case
      apply (cases a) apply auto
      apply (cases i) apply auto
      apply (cases i) by auto
  qed
  ultimately show ?thesis by simp
qed

lemma a: "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> (\<forall>i \<in> set is. i < length (vertices f)) \<Longrightarrow>
 (\<And>a. a < length (vertices f) \<Longrightarrow> hideDupsRec ((f \<bullet> ^^ a) v) [(f \<bullet> ^^ k) v. k \<leftarrow> is] = natToVertexListRec a v f is)"
proof (induct "is")
  case Nil then show ?case by simp
next
  case (Cons i "is") then show ?case
   by (auto simp: nextVertices_def intro: nextVertex_inj)
qed

lemma indexToVertexList_natToVertexList_eq: "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow>
  (\<forall>i \<in> set is. i < length (vertices f)) \<Longrightarrow> is \<noteq> [] \<Longrightarrow>
 hd is = 0 \<Longrightarrow> indexToVertexList f v is = natToVertexList v f is"
apply (cases "is") by (auto simp: a [where a = 0, simplified] indexToVertexList_def nextVertices_def)



(********************* Einschub Ende ***************************************)


(******** natToVertexListRec ************)

lemma nvlr_length: "\<And> old.  (length (natToVertexListRec old v f ls)) = length ls"
apply (induct ls) by auto

lemma nvl_length[simp]: "hd e = 0 \<Longrightarrow> length (natToVertexList v f e) = length e"
apply (cases "e")
by (auto intro: nvlr_length)


lemma natToVertexListRec_length[simp]: "\<And> e f. length (natToVertexListRec e v f es) = length es"
by (induct es) auto

lemma natToVertexList_length[simp]: "incrIndexList es (length es) (length (vertices f)) \<Longrightarrow>
length (natToVertexList v f es) = length es" apply (case_tac es) by simp_all


lemma  natToVertexList_nth_Suc: "incrIndexList es (length es) (length (vertices f)) \<Longrightarrow> Suc n < length es \<Longrightarrow>
(natToVertexList v f es)!(Suc n) = (if (es!n = es!(Suc n)) then None else Some (f\<^bsup>(es!Suc n)\<^esup> \<bullet> v))"
proof -
  assume incr: "incrIndexList es (length es) (length (vertices f))" and n: "Suc n < length es"
  have rec: "\<And> old n. Suc n < length es \<Longrightarrow>
    (natToVertexListRec old v f es)!(Suc n) = (if (es!n = es!(Suc n)) then None else Some (f\<^bsup>(es!Suc n)\<^esup> \<bullet> v))"
  proof (induct es)
    case Nil then show ?case by auto
  next
    case (Cons e es)
    note cons1 = this
    then show ?case
    proof (cases es)
      case Nil with cons1 show ?thesis by simp
    next
      case (Cons e' es')
      with cons1 show ?thesis
      proof (cases n)
        case 0 with Cons cons1 show ?thesis by simp
      next
        case (Suc m) with Cons cons1
        have "\<And> old. natToVertexListRec old v f es ! Suc m = (if es ! m = es ! Suc m then None else Some (f\<^bsup>es ! Suc m\<^esup> \<bullet> v))"
          by (rule_tac cons1) auto
        then show ?thesis apply (cases "e = old") by (simp_all add: Suc)
      qed
    qed
  qed
  with  n have "natToVertexListRec 0 v f es ! Suc n = (if es ! n = es ! Suc n then None else Some (f\<^bsup>es ! Suc n\<^esup> \<bullet> v))" by (rule_tac rec) auto
  with incr show ?thesis by (cases es) auto
qed

lemma  natToVertexList_nth_0: "incrIndexList es (length es) (length (vertices f)) \<Longrightarrow> 0 < length es \<Longrightarrow>
(natToVertexList v f es)!0 = Some (f\<^bsup>(es!0)\<^esup> \<bullet> v)"
 apply (cases es) 
 apply (simp_all add: nextVertices_def)
 by (subgoal_tac "a = 0")  auto

lemma  natToVertexList_hd[simp]:
  "incrIndexList es (length es) (length (vertices f)) \<Longrightarrow> hd (natToVertexList v f es) = Some v"
  apply (cases es) by (simp_all add: nextVertices_def)

lemma nth_last[intro]: "Suc i = length xs \<Longrightarrow>  xs!i = last xs"
by (cases xs rule: rev_exhaust)  auto


declare incrIndexList_help4 [simp del]

lemma natToVertexList_last[simp]:
  "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> incrIndexList es (length es) (length (vertices f)) \<Longrightarrow> last (natToVertexList v f es) = Some (last (verticesFrom f v))"
proof -
  assume vors: "distinct (vertices f)" "v \<in> \<V> f" and incr: "incrIndexList es (length es) (length (vertices f))"
  define n' where "n' = length es - 2"
  from incr have "1 < length es" by auto
  with n'_def have n'l: "Suc (Suc n') = length es" by arith
  from incr n'l have last_ntvl: "(natToVertexList v f es)!(Suc n') = last (natToVertexList v f es)" by auto
  from n'l have last_es: "es!(Suc n') = last es" by auto
  from n'l  have "es!n' = last (butlast es)" apply (cases es rule: rev_exhaust) by (auto simp: nth_append)
  with last_es incr have less: "es!n' < es!(Suc n')" by auto
  from n'l have "Suc n' < length es" by arith
  with incr less have "(natToVertexList v f es)!(Suc n') = (Some (f\<^bsup>(es!Suc n')\<^esup> \<bullet> v))" by (auto dest: natToVertexList_nth_Suc)
  with incr last_ntvl last_es have rule1: "last (natToVertexList v f es) = Some (f\<^bsup>((length (vertices f)) - (Suc 0))\<^esup> \<bullet> v)" by auto

  from incr have lvf: "1 < length (vertices f)" by auto
  with vors have rule2: "verticesFrom f v ! ((length (vertices f)) - (Suc 0)) = f\<^bsup>((length (vertices f)) - (Suc 0))\<^esup> \<bullet> v" by (auto intro!: verticesFrom_nth)

  from vors lvf have "verticesFrom f v ! ((length (vertices f)) - (Suc 0)) = last (verticesFrom f v)"
    apply (rule_tac nth_last)
    by (auto simp: verticesFrom_length)
  with rule1 rule2 show ?thesis by auto
qed

lemma indexToVertexList_last[simp]:
  "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> incrIndexList es (length es) (length (vertices f)) \<Longrightarrow> last (indexToVertexList f v es) = Some (last (verticesFrom f v))"
apply (subgoal_tac "indexToVertexList f v es = natToVertexList v f es") apply simp
apply (rule indexToVertexList_natToVertexList_eq) by auto

lemma nths_take: "\<And> n iset. \<forall> i \<in> iset. i < n \<Longrightarrow> nths (take n xs) iset = nths xs iset"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) then show ?case apply (simp add: nths_Cons) apply (cases n) apply simp apply (simp add: nths_Cons) apply (rule Cons) by auto
qed


lemma nths_reduceIndices: "\<And> iset. nths xs iset = nths xs {i. i < length xs \<and> i \<in> iset}"
proof (induct xs)
  case Nil then show ?case by simp
next
  case (Cons x xs) then
  have "nths xs {j. Suc j \<in> iset} = nths xs {i. i < length xs \<and> i \<in> {j. Suc j \<in> iset}}" by (rule_tac Cons)
  then show ?case by (simp add: nths_Cons)
qed

lemma natToVertexList_nths1: "distinct (vertices f) \<Longrightarrow>
  v \<in> \<V> f \<Longrightarrow> vs = verticesFrom f v \<Longrightarrow>
  incrIndexList es (length es) (length vs) \<Longrightarrow> n \<le>  length es \<Longrightarrow>
  nths (take (Suc (es!(n - 1))) vs) (set (take n es))
  = removeNones (take n (natToVertexList v f es))"
proof (induct n)
  case 0 then show ?case by simp
next
  case (Suc n)
  then have "nths (take (Suc (es ! (n - Suc 0))) (verticesFrom f v)) (set (take n es)) = removeNones (take n (natToVertexList v f es))"
    "distinct (vertices f)" "v \<in> \<V> f" "vs = verticesFrom f v" "incrIndexList es (length es) (length (verticesFrom f v))" "Suc n \<le> length es" by auto  (* does this improve the performance? *)
  note suc1 = this
  then have lvs: "length vs = length (vertices f)" by (auto intro: verticesFrom_length)
  with suc1 have vsne: "vs \<noteq> []" by auto
  with suc1 show ?case
  proof (cases "natToVertexList v f es ! n")
    case None then show ?thesis
    proof (cases n)
      case 0 with None suc1 lvs show ?thesis by (simp add: take_Suc_conv_app_nth natToVertexList_nth_0)
    next
      case (Suc n')
      with None suc1 lvs have esn: "es!n = es!n'" by (simp add: natToVertexList_nth_Suc split: if_split_asm)
      from Suc have n': "n - Suc 0 = n'" by auto
      show ?thesis
      proof (cases "Suc n = length es")
        case True then
        have small_n: "n < length es" by auto
        from True have "take (Suc n) es = es" by auto
        with small_n have "take n es @ [es!n] = es" by (simp add: take_Suc_conv_app_nth)
        then have esn_simps: "take n es = butlast es \<and>  es!n = last es" by (cases es rule: rev_exhaust) auto

        from True Suc have n'l: "Suc n' = length (butlast es)" by auto
        then have small_n': "n' < length (butlast es)" by auto

        from Suc small_n have take_n': "take (Suc n') (butlast es @ [last es]) = take (Suc n') (butlast es)" by auto
        
        from small_n have es_exh: "es = butlast es @ [last es]" by (cases es rule: rev_exhaust) auto
        
        from n'l have "take (Suc n') (butlast es @ [last es]) = butlast es" by auto
        with es_exh have "take (Suc n') es = butlast es" by auto
        with small_n Suc have "take n' es @ [es!n'] = (butlast es)" by (simp add: take_Suc_conv_app_nth)
        with small_n' have esn'_simps: "take n' es = butlast (butlast es) \<and>  es!n' = last (butlast es)"
          by (cases "butlast es" rule: rev_exhaust) auto

        from suc1 have "last (butlast es) < last es" by auto
        with esn esn_simps esn'_simps have False by auto (* have "last (butlast es) = last es" by auto  *)
        then show ?thesis by auto
      next
        case False with suc1 have le: "Suc n < length es" by auto
        from suc1 le have "es = take (Suc n) es @ es!(Suc n) # drop (Suc (Suc n)) es" by (auto intro: id_take_nth_drop)
        with suc1 have "increasing (take (Suc n) es @ es!(Suc n) # drop (Suc (Suc n)) es)" by auto
        then have "\<forall> i \<in> (set (take (Suc n) es)). i \<le>  es ! (Suc n)" by (auto intro: increasing2)
        with suc1 have  "\<forall> i \<in> (set (take n es)). i \<le>  es ! (Suc n)" by (simp add: take_Suc_conv_app_nth)
        then have seq: "nths (take (Suc (es ! Suc n)) (verticesFrom f v)) (set (take n es))
          = nths (verticesFrom f v) (set (take n es))"
          apply (rule_tac nths_take) by auto
        from suc1 have "es = take n es @ es!n # drop (Suc n) es" by (auto intro: id_take_nth_drop)
        with suc1 have "increasing (take n es @ es!n # drop (Suc n) es)" by auto
        then have "\<forall> i \<in> (set (take n es)). i \<le>  es ! n" by (auto intro: increasing2)
        with suc1 esn have  "\<forall> i \<in> (set (take n es)). i \<le>  es ! n'" by (simp add: take_Suc_conv_app_nth)
        with Suc have seq2: "nths (take (Suc (es ! n')) (verticesFrom f v)) (set (take n es))
         = nths  (verticesFrom f v) (set (take n es))"
          apply (rule_tac nths_take) by auto
        from Suc suc1 have "(insert (es ! n') (set (take n es))) = set (take n es)"
        apply auto by (simp add: take_Suc_conv_app_nth)
        with esn None suc1 seq seq2 n' show ?thesis by (simp add: take_Suc_conv_app_nth)
      qed
    qed
  next
    case (Some v') then show ?thesis
    proof (cases n)
      case 0
      from suc1 lvs have "verticesFrom f v \<noteq> []" by auto
      then have "verticesFrom f v = hd (verticesFrom f v) # tl (verticesFrom f v)" by auto
      then have "verticesFrom f v = v # tl (verticesFrom f v)" by (simp add: verticesFrom_hd)
      then obtain z where "verticesFrom f v = v # z" by auto
      then have sub: "nths (verticesFrom f v) {0} = [v]" by (auto simp: nths_Cons)
      from 0 suc1 have "es!0 = 0" by (cases es)  auto
      with 0 Some suc1 lvs sub vsne show ?thesis
        by (simp add: take_Suc_conv_app_nth natToVertexList_nth_0 nextVertices_def take_Suc
        nths_Cons verticesFrom_hd del:verticesFrom_empty)
    next
      case (Suc n')
      with Some suc1 lvs have esn: "es!n \<noteq> es!n'" by (simp add: natToVertexList_nth_Suc split: if_split_asm)
      from suc1 Suc have "Suc n' < length es" by auto
      with suc1 lvs esn  have "natToVertexList v f es !(Suc n') = Some (f\<^bsup>(es!(Suc n'))\<^esup> \<bullet> v)"
      apply (simp add: natToVertexList_nth_Suc)
        by (simp add: Suc)
      with Suc have "natToVertexList v f es ! n = Some (f\<^bsup>(es!n)\<^esup> \<bullet> v)" by auto
      with Some have v': "v' = f\<^bsup>(es!n)\<^esup> \<bullet> v" by simp
      from Suc have n': "n - Suc 0 = n'" by auto
      from suc1 Suc have "es = take (Suc n') es @ es!n # drop (Suc n) es" by (auto intro: id_take_nth_drop)
      with suc1 have  "increasing (take (Suc n') es @ es!n # drop (Suc n) es)" by auto
      with suc1 Suc have "es!n' \<le>  es!n" apply (auto intro!: increasing2)
      by (auto simp: take_Suc_conv_app_nth)
      with esn have smaller_n: "es!n' < es!n" by auto
      from suc1 lvs have smaller: "(es!n) < length vs" by auto
      from suc1 smaller lvs have "(verticesFrom f v)!(es!n) =  f\<^bsup>(es!n)\<^esup> \<bullet> v" by (auto intro: verticesFrom_nth)
      with v' have "(verticesFrom f v)!(es!n) = v'" by auto
      then have sub1: "nths ([((verticesFrom f v)!(es!n))])
          {j. j + (es!n) : (insert (es ! n) (set (take n es)))} = [v']" by auto

      from suc1 smaller lvs have len: "length (take (es ! n) (verticesFrom f v)) = es!n" by auto

      have "\<And>x. x \<in> (set (take n es)) \<Longrightarrow> x < (es ! n)"
      proof -
        fix x
        assume x: "x \<in> set (take n es)"
        from suc1 Suc have "es = take n' es @ es!n' # drop (Suc n') es" by (auto intro: id_take_nth_drop)
        with suc1 have "increasing (take n' es @ es!n' # drop (Suc n') es)" by auto
        then have "\<And> x. x \<in> set (take n' es) \<Longrightarrow> x \<le> es!n'" by (auto intro!: increasing2)
        with x Suc suc1 have "x \<le> es!n'" by (auto simp: take_Suc_conv_app_nth)
        with smaller_n show "x < es!n" by auto
      qed
      then have "{i. i < es ! n \<and> i \<in> set (take n es)} = (set (take n es))" by auto
      then have elim_insert: "{i. i < es ! n \<and> i \<in> insert (es ! n) (set (take n es))} = (set (take n es))" by auto

      have "nths (take (es ! n) (verticesFrom f v)) (insert (es ! n) (set (take n es))) =
        nths (take (es ! n) (verticesFrom f v)) {i. i < length (take (es ! n) (verticesFrom f v))
         \<and> i \<in> (insert (es ! n) (set (take n es)))}" by (rule nths_reduceIndices)
      with len have "nths (take (es ! n) (verticesFrom f v)) (insert (es ! n) (set (take n es))) =
        nths (take (es ! n) (verticesFrom f v)) {i. i < (es ! n) \<and> i \<in> (insert (es ! n) (set (take n es)))}"
        by simp
      with elim_insert have sub2: "nths (take (es ! n) (verticesFrom f v)) (insert (es ! n) (set (take n es))) =
        nths (take (es ! n) (verticesFrom f v)) (set (take n es))" by simp

      define m where "m = es!n - es!n'"
      with smaller_n have mgz: "0 < m" by auto
      with m_def have esn: "es!n = (es!n') + m" by auto

      have helper: "\<And>x. x \<in> (set (take n es)) \<Longrightarrow> x \<le>  (es ! n')"
      proof -
        fix x
        assume x: "x \<in> set (take n es)"
        from suc1 Suc have "es = take n' es @ es!n' # drop (Suc n') es" by (auto intro: id_take_nth_drop)
        with suc1 have "increasing (take n' es @ es!n' # drop (Suc n') es)" by auto
        then have "\<And> x. x \<in> set (take n' es) \<Longrightarrow> x \<le> es!n'" by (auto intro!: increasing2)
        with x Suc suc1 show "x \<le> es!n'" by (auto simp: take_Suc_conv_app_nth)
      qed

      define m' where "m' = m - 1"
      define Suc_es_n' where "Suc_es_n' = Suc (es!n')"

      from smaller smaller_n have "Suc (es!n') < length vs" by auto
      then have "min (length vs) (Suc (es ! n')) = Suc (es!n')" by arith
      with Suc_es_n'_def have empty: "{j. j + length (take Suc_es_n' vs) \<in> set (take n es)} = {}"
        apply auto apply (frule helper) by arith


      from Suc_es_n'_def mgz esn m'_def have esn': "es!n = Suc_es_n' + m'" by auto

      with smaller have "(take (Suc_es_n' + m') vs) = take (Suc_es_n') vs @ take m' (drop (Suc_es_n') vs)"
        by (auto intro: take_add)
      with esn' have "nths (take (es ! n) vs) (set (take n es))
         = nths (take (Suc_es_n') vs @ take m' (drop (Suc_es_n') vs)) (set (take n es))" by auto
      then have "nths (take (es ! n) vs) (set (take n es)) =
        nths (take (Suc_es_n') vs) (set (take n es)) @
        nths (take m' (drop (Suc_es_n') vs)) {j. j + length (take (Suc_es_n') vs) : (set (take n es))}"
        by (simp add: nths_append)
      with empty Suc_es_n'_def have "nths (take (es ! n) vs) (set (take n es)) =
        nths (take (Suc (es!n')) vs) (set (take n es))" by simp
      with suc1 sub2 have sub3: "nths (take (es ! n) (verticesFrom f v)) (insert (es ! n) (set (take n es))) =
        nths (take (Suc (es!n')) (verticesFrom f v)) (set (take n es))" by simp
        
      from smaller suc1 have "take (Suc (es ! n)) (verticesFrom f v)
       = take (es ! n) (verticesFrom f v) @ [((verticesFrom f v)!(es!n))]"
       by (auto simp: take_Suc_conv_app_nth)
      with suc1 smaller have
        "nths (take (Suc (es ! n)) (verticesFrom f v)) (insert (es ! n) (set (take n es))) =
         nths (take (es ! n) (verticesFrom f v)) (insert (es ! n) (set (take n es)))
         @ nths ([((verticesFrom f v)!(es!n))])  {j. j + (es!n) : (insert (es ! n) (set (take n es)))}"
        by (auto simp: nths_append)
      with sub1 sub3 have "nths (take (Suc (es ! n)) (verticesFrom f v)) (insert (es ! n) (set (take n es)))
       = nths (take (Suc (es ! n')) (verticesFrom f v)) (set (take n es)) @ [v']" by auto
      with Some suc1 lvs n' show ?thesis by (simp add: take_Suc_conv_app_nth)
    qed
  qed
qed

lemma natToVertexList_nths: "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow>
  incrIndexList es (length es) (length (vertices f)) \<Longrightarrow>
  nths (verticesFrom f v) (set es) = removeNones (natToVertexList v f es)"
proof -
  assume vors1: "distinct (vertices f)" "v \<in> \<V> f"
     "incrIndexList es (length es) (length (vertices f))"
  define vs where "vs = verticesFrom f v"
  with vors1 have lvs: "length vs = length (vertices f)"  by (auto intro: verticesFrom_length)
  with vors1 vs_def have vors: "distinct (vertices f)" "v \<in> \<V> f"
    "vs = verticesFrom f v"  "incrIndexList es (length es) (length vs)" by auto

  with lvs have vsne: "vs \<noteq> []" by auto
  define n where "n = length es"
  then have "es!(n - 1) = last es"
  proof (cases n)
    case 0 with n_def vors show ?thesis by (cases es)  auto
  next
    case (Suc n')
    with n_def have small_n': "n' < length es" by arith
    from Suc n_def have "take (Suc n') es = es" by auto
    with small_n' have "take n' es @ [es!n'] = es" by (simp add: take_Suc_conv_app_nth)
    then have "es!n' = last es" by (cases es rule: rev_exhaust) auto
    with Suc show ?thesis by auto
  qed
  with vors have "es!(n - 1) = (length vs) - 1" by auto
  with vsne have "Suc (es! (n - 1)) = (length vs)" by auto
  then have take_vs: "take (Suc (es!(n - 1))) vs = vs" by auto

  from n_def vors have "n =  length (natToVertexList v f es)" by auto
  then have take_nTVL: "take n (natToVertexList v f es) = natToVertexList v f es" by auto

  from n_def have take_es: "take n es = es" by auto

  from n_def have "n \<le> length es" by auto
  with vors   have "nths (take (Suc (es!(n - 1))) vs) (set (take n es))
    = removeNones (take n (natToVertexList v f es))" by (rule natToVertexList_nths1)
  with take_vs take_nTVL take_es vs_def show ?thesis by simp
qed


lemma filter_Cons2:
 "x \<notin> set ys \<Longrightarrow> [y\<leftarrow>ys.  y = x \<or> P y] = [y\<leftarrow>ys. P y]"
 by (induct ys) (auto)

lemma natToVertexList_removeNones:
  "distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow>
  incrIndexList es (length es) (length (vertices f)) \<Longrightarrow>
  [x\<leftarrow>verticesFrom f v. x \<in> set (removeNones (natToVertexList v f es))]
 = removeNones (natToVertexList v f es)"
proof -
  assume vors: "distinct (vertices f)" "v \<in> \<V> f"
    "incrIndexList es (length es) (length (vertices f))"
  then have dist: "distinct (verticesFrom f v)" by auto
  from vors have sub_eq: "nths (verticesFrom f v) (set es)
    = removeNones (natToVertexList v f es)" by (rule natToVertexList_nths)
  from dist have "[x \<leftarrow> verticesFrom f v.
    x \<in> set (nths (verticesFrom f v) (set es))] = removeNones (natToVertexList v f es)"
  apply (simp add: filter_in_nths)
    by (simp add: sub_eq)
  with sub_eq show ?thesis by simp
qed

(**************************** invalidVertexList ************)

definition is_duplicateEdge :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> bool" where
 "is_duplicateEdge g f a b \<equiv>
   ((a, b) \<in> edges g \<and> (a, b) \<notin> edges f \<and> (b, a) \<notin> edges f)
 \<or> ((b, a) \<in> edges g \<and> (b, a) \<notin> edges f \<and> (a, b) \<notin> edges f)"

definition invalidVertexList :: "graph \<Rightarrow> face \<Rightarrow> vertex option list \<Rightarrow> bool" where
 "invalidVertexList g f vs \<equiv>
     \<exists>i < |vs|- 1.
         case vs!i of None \<Rightarrow> False
             | Some a \<Rightarrow> case vs!(i+1) of None \<Rightarrow> False
             | Some b \<Rightarrow> is_duplicateEdge g f a b"


(**************************** subdivFace **********************)

subsection \<open>\<open>pre_subdivFace(')\<close>\<close>

definition pre_subdivFace_face :: "face \<Rightarrow> vertex \<Rightarrow> vertex option list \<Rightarrow> bool" where
"pre_subdivFace_face f v' vOptionList \<equiv>
     [v \<leftarrow> verticesFrom f v'. v \<in> set (removeNones vOptionList)]
       = (removeNones vOptionList)
  \<and> \<not> final f \<and> distinct (vertices f)
  \<and> hd (vOptionList) = Some v'
  \<and> v' \<in> \<V> f
  \<and> last (vOptionList) =  Some (last (verticesFrom f v'))
  \<and> hd (tl (vOptionList)) \<noteq> last (vOptionList)
  \<and> 2 < | vOptionList |
  \<and> vOptionList \<noteq>  []
  \<and> tl (vOptionList) \<noteq> []"

definition pre_subdivFace :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> vertex option list \<Rightarrow> bool" where
"pre_subdivFace g f v' vOptionList \<equiv>
  pre_subdivFace_face f v' vOptionList \<and> \<not> invalidVertexList g f vOptionList"

(* zu teilende Fläche, ursprüngliches v, erster Ram-Punkt, Anzahl der überlaufenen NOnes, rest der vol *)
definition pre_subdivFace' :: "graph \<Rightarrow> face \<Rightarrow> vertex \<Rightarrow> vertex \<Rightarrow> nat \<Rightarrow> vertex option list \<Rightarrow> bool" where
"pre_subdivFace' g f v' ram1 n vOptionList \<equiv>
  \<not> final f \<and> v' \<in> \<V> f \<and> ram1 \<in> \<V> f
  \<and> v' \<notin> set (removeNones vOptionList)
  \<and> distinct (vertices f)
  \<and> (
    [v \<leftarrow> verticesFrom f v'. v \<in> set (removeNones vOptionList)]
        =  (removeNones vOptionList)
  \<and> before (verticesFrom f v') ram1 (hd (removeNones vOptionList))
  \<and> last (vOptionList) =  Some (last (verticesFrom f v'))
  \<and> vOptionList \<noteq>  []
  \<and> ((v' = ram1 \<and> (0 < n)) \<or> ((v' = ram1 \<and> (hd (vOptionList) \<noteq> Some (last (verticesFrom f v'))))  \<or> (v' \<noteq> ram1)))
  \<and> \<not> invalidVertexList g f vOptionList
  \<and> (n = 0 \<and> hd (vOptionList) \<noteq> None \<longrightarrow>  \<not> is_duplicateEdge g f ram1 (the (hd (vOptionList))))
  \<or> (vOptionList = [] \<and> v' \<noteq> ram1)
  )"


lemma pre_subdivFace_face_in_f[intro]: "pre_subdivFace_face f v ls \<Longrightarrow> Some a \<in> set ls \<Longrightarrow> a \<in> set (verticesFrom f v)"
  apply (subgoal_tac "a \<in> set (removeNones ls)") apply (auto  simp: pre_subdivFace_face_def)
  apply (subgoal_tac "a \<in> set [v\<leftarrow>verticesFrom f v . v \<in> set (removeNones ls)]")
  apply (thin_tac "[v\<leftarrow>verticesFrom f v . v \<in> set (removeNones ls)] = removeNones ls") by auto

lemma pre_subdivFace_in_f[intro]: "pre_subdivFace g f v ls \<Longrightarrow> Some a \<in> set ls \<Longrightarrow> a \<in> set (verticesFrom f v)"
 by (auto simp: pre_subdivFace_def)


lemma pre_subdivFace_face_in_f'[intro]: "pre_subdivFace_face f v ls \<Longrightarrow> Some a \<in> set ls \<Longrightarrow> a \<in> \<V> f"
  apply (cases "a = v") apply (force simp: pre_subdivFace_face_def)
 apply (rule verticesFrom_in') apply (rule pre_subdivFace_face_in_f)
by auto


lemma filter_congs_shorten1: "distinct (verticesFrom f v) \<Longrightarrow> [v\<leftarrow>verticesFrom f v . v = a \<or> v \<in> set vs] = (a # vs)
    \<Longrightarrow> [v\<leftarrow>verticesFrom f v . v \<in> set vs] = vs"
proof -
  assume dist: "distinct (verticesFrom f v)" and eq: "[v\<leftarrow>verticesFrom  f v . v = a \<or> v \<in> set vs] = (a # vs)"
  have rule1: "\<And> vs a ys. distinct vs \<Longrightarrow> [v\<leftarrow>vs . v = a \<or> v \<in> set ys] = a # ys \<Longrightarrow> [v\<leftarrow>vs. v \<in> set ys] = ys"
  proof -
    fix vs a ys
    assume dist: "distinct vs" and ays:  "[v\<leftarrow>vs . v = a \<or> v \<in> set ys] = a # ys"
    then have "distinct ([v\<leftarrow>vs . v = a \<or> v \<in> set ys])" by (rule_tac distinct_filter)
    with ays have distys: "distinct (a # ys)" by simp
    from dist distys ays show "[v\<leftarrow>vs. v \<in> set ys] = ys"
     apply (induct vs) by (auto  split: if_split_asm simp: filter_Cons2)
  qed

  from dist eq show ?thesis  by (rule_tac rule1)
qed

lemma ovl_shorten: "distinct (verticesFrom f v) \<Longrightarrow>
  [v\<leftarrow>verticesFrom f v . v \<in> set (removeNones (va # vol))] = (removeNones (va # vol))
    \<Longrightarrow> [v\<leftarrow>verticesFrom f v . v \<in> set (removeNones (vol))] =  (removeNones (vol))"
proof -
  assume dist: "distinct (verticesFrom f v)"
  and vors: "[v\<leftarrow>verticesFrom f v . v \<in> set (removeNones (va # vol))] = (removeNones (va # vol))"
  then show ?thesis
  proof (cases va)
    case None with vors Cons show ?thesis by auto
  next
    case (Some a) with vors dist show ?thesis by (auto intro!: filter_congs_shorten1)
  qed
qed

lemma pre_subdivFace_face_distinct: "pre_subdivFace_face f v vol \<Longrightarrow> distinct (removeNones vol)"
  apply (auto dest!: verticesFrom_distinct simp: pre_subdivFace_face_def)
  apply (subgoal_tac "distinct ([v\<leftarrow>verticesFrom f v . v \<in> set (removeNones vol)])") apply simp
  apply (thin_tac "[v\<leftarrow>verticesFrom f v . v \<in> set (removeNones vol)] = removeNones vol") by auto

lemma invalidVertexList_shorten: "invalidVertexList g f vol \<Longrightarrow> invalidVertexList g f (v # vol)"
apply (simp add: invalidVertexList_def) apply auto apply (rule exI) apply safe
apply (subgoal_tac "(Suc i) < | vol |") apply assumption apply arith
apply auto apply (case_tac "vol!i") by auto

lemma pre_subdivFace_pre_subdivFace': "v \<in> \<V> f \<Longrightarrow> pre_subdivFace g f v (vo # vol) \<Longrightarrow>
  pre_subdivFace' g f v v 0 (vol)"
proof -
  assume vors:  "v \<in> \<V> f"  "pre_subdivFace g f v (vo # vol)"
  then have vors': "v \<in> \<V> f" "pre_subdivFace_face f v (vo # vol)" "\<not> invalidVertexList g f (vo # vol)"
    by (auto simp: pre_subdivFace_def)
  then have r: "removeNones vol \<noteq> []" apply (cases "vol" rule: rev_exhaust) by  (auto  simp: pre_subdivFace_face_def)
  then have "Some (hd (removeNones vol)) \<in> set vol" apply (induct vol) apply auto apply (case_tac a) by auto
  then have "Some (hd (removeNones vol)) \<in> set (vo # vol)" by auto
  with vors' have hd: "hd (removeNones vol) \<in> \<V> f" by (rule_tac pre_subdivFace_face_in_f')

  from vors' have "Some v = vo" by (auto  simp: pre_subdivFace_face_def)
  with vors'  have "v \<notin> set (tl (removeNones (vo # vol)))" apply (drule_tac pre_subdivFace_face_distinct) by auto
  with vors' r have ne: "v \<noteq> hd (removeNones vol)" by (cases  "removeNones vol")  (auto  simp: pre_subdivFace_face_def)

  from vors' have dist: "distinct (removeNones (vo # vol))"  apply (rule_tac pre_subdivFace_face_distinct) .

  from vors' have invalid: "\<not> invalidVertexList g f vol" by (auto simp: invalidVertexList_shorten)


  from ne hd vors' invalid dist show ?thesis apply (unfold pre_subdivFace'_def)
    apply (simp add: pre_subdivFace'_def pre_subdivFace_face_def)
    apply safe
        apply (rule ovl_shorten)
         apply (simp add: pre_subdivFace_face_def) apply assumption
       apply (rule before_verticesFrom)
          apply simp+
    apply (simp add: invalidVertexList_def)
    apply (erule allE)
    apply (erule impE)
    apply (subgoal_tac "0 <  |vol|")
      apply (thin_tac "Suc 0 < | vol |")
      apply  assumption
     apply simp
    apply (simp)
    apply (case_tac "vol") apply simp by (simp add: is_duplicateEdge_def)
qed


lemma pre_subdivFace'_distinct: "pre_subdivFace' g f v' v n vol \<Longrightarrow> distinct (removeNones vol)"
  apply (unfold pre_subdivFace'_def)
  apply (cases vol) apply simp+
  apply (elim conjE)
  apply (drule_tac verticesFrom_distinct) apply assumption
  apply (subgoal_tac "distinct [v\<leftarrow>verticesFrom f v' . v \<in> set (removeNones (a # list))]") apply force
  apply (thin_tac "[v\<leftarrow>verticesFrom f v' . v \<in> set (removeNones (a # list))] = removeNones (a # list)")
  by auto


lemma natToVertexList_pre_subdivFace_face:
 "\<not> final f \<Longrightarrow> distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> 2 < |es| \<Longrightarrow>
 incrIndexList es (length es) (length (vertices f)) \<Longrightarrow>
 pre_subdivFace_face f v (natToVertexList v f es)"
proof -
  assume vors: "\<not> final f" "distinct (vertices f)" "v \<in> \<V> f" "2 < |es|"
     "incrIndexList es (length es) (length (vertices f))"
  then have lastOvl: "last (natToVertexList v f es) =  Some (last (verticesFrom f v))" by auto

  from vors have nvl_l: "2 < | natToVertexList v f es |"
    by auto

  from vors have "distinct [x\<leftarrow>verticesFrom f v . x \<in> set (removeNones (natToVertexList v f es))]" by auto
  with vors have "distinct (removeNones (natToVertexList v f es))" by (simp add: natToVertexList_removeNones)
  with nvl_l lastOvl have hd_last: "hd (tl (natToVertexList v f es)) \<noteq> last (natToVertexList v f es)" apply auto
    apply (cases "natToVertexList v f es") apply simp
    apply (case_tac "list" rule: rev_exhaust) apply simp
    apply (case_tac "ys") apply simp
    apply (case_tac "a") apply simp by simp

  from vors lastOvl hd_last nvl_l show ?thesis
    apply (auto intro: natToVertexList_removeNones simp: pre_subdivFace_face_def)
    apply (cases es) apply auto
    apply (cases es) apply auto
    apply (subgoal_tac "0 < length list") apply (case_tac list) by (auto split: if_split_asm)
qed


lemma indexToVertexList_pre_subdivFace_face:
 "\<not> final f \<Longrightarrow> distinct (vertices f) \<Longrightarrow> v \<in> \<V> f \<Longrightarrow> 2 < |es| \<Longrightarrow>
 incrIndexList es (length es) (length (vertices f)) \<Longrightarrow>
 pre_subdivFace_face f v (indexToVertexList f v es)"
apply (subgoal_tac "indexToVertexList f v es = natToVertexList v f es") apply simp
apply (rule natToVertexList_pre_subdivFace_face) apply assumption+
apply (rule indexToVertexList_natToVertexList_eq) by auto

lemma subdivFace_subdivFace'_eq: "pre_subdivFace g f v vol \<Longrightarrow>  subdivFace g f vol = subdivFace' g f v 0 (tl vol)"
by (simp_all add: subdivFace_def pre_subdivFace_def pre_subdivFace_face_def)

lemma pre_subdivFace'_None:
 "pre_subdivFace' g f v' v n (None # vol) \<Longrightarrow>
  pre_subdivFace' g f v' v (Suc n) vol"
by(auto simp: pre_subdivFace'_def dest:invalidVertexList_shorten
        split:if_split_asm)

declare verticesFrom_between [simp del]


(* zu zeigen:
 1. vol \<noteq> [] \<Longrightarrow> [v\<in>verticesFrom f21 v' . v \<in> set (removeNones vol)] = removeNones vol
 2. vol \<noteq> [] \<Longrightarrow> before (verticesFrom f21 v') u (hd (removeNones vol))
 3. vol \<noteq> [] \<Longrightarrow> distinct (vertices f21)
 4. vol \<noteq> [] \<Longrightarrow> last vol = Some (last (verticesFrom f21 v'))
*)

lemma verticesFrom_split: "v # tl (verticesFrom f v) = verticesFrom f v" by (auto simp: verticesFrom_Def)

lemma verticesFrom_v: "distinct (vertices f) \<Longrightarrow> vertices f = a @ v # b \<Longrightarrow> verticesFrom f v = v # b @ a"
by (simp add: verticesFrom_Def)


lemma splitAt_fst[simp]: "distinct xs \<Longrightarrow> xs = a @ v # b \<Longrightarrow> fst (splitAt v xs) = a"
by auto

lemma splitAt_snd[simp]: "distinct xs \<Longrightarrow> xs = a @ v # b \<Longrightarrow> snd (splitAt v xs) = b"
by auto

lemma verticesFrom_splitAt_v_fst[simp]:
  "distinct (verticesFrom f v) \<Longrightarrow> fst (splitAt v (verticesFrom f v)) = []"
  by (simp add: verticesFrom_Def)
lemma verticesFrom_splitAt_v_snd[simp]:
  "distinct (verticesFrom f v) \<Longrightarrow> snd (splitAt v (verticesFrom f v)) = tl (verticesFrom f v)"
  by (simp add: verticesFrom_Def)


lemma filter_distinct_at:
  "distinct xs \<Longrightarrow> xs = (as @ u # bs) \<Longrightarrow> [v\<leftarrow>xs. v = u \<or> P v] = u # us \<Longrightarrow>
  [v\<leftarrow>bs. P v] = us \<and> [v\<leftarrow>as. P v] = []"
apply (subgoal_tac "filter P as @ u # filter P bs = [] @ u # us")
apply (drule local_help')  by (auto simp: filter_Cons2)

lemma filter_distinct_at3: "distinct xs \<Longrightarrow> xs = (as @ u # bs) \<Longrightarrow>
  [v\<leftarrow>xs. v = u \<or> P v] = u # us \<Longrightarrow> \<forall> z \<in> set zs. z \<in> set as \<or> \<not> ( P z) \<Longrightarrow>
  [v\<leftarrow>zs@bs. P v] = us"
apply (drule filter_distinct_at) apply assumption+ apply simp
by (induct zs) auto

lemma filter_distinct_at4: "distinct xs \<Longrightarrow> xs = (as @ u # bs)
  \<Longrightarrow> [v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us
  \<Longrightarrow> set zs \<inter> set us \<subseteq> {u} \<union> set as
  \<Longrightarrow> [v \<leftarrow> zs@bs. v \<in> set us] = us"
proof -
  assume vors: "distinct xs" "xs = (as @ u # bs)"
    "[v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us"
    "set zs \<inter> set us \<subseteq> {u} \<union> set as"
  then have "distinct ([v\<leftarrow>xs. v = u \<or> v \<in> set us])"  apply (rule_tac distinct_filter) by simp
  with vors have dist: "distinct (u # us)" by auto
  with vors show ?thesis
  apply (rule_tac filter_distinct_at3) by assumption+  auto
qed

lemma filter_distinct_at5: "distinct xs \<Longrightarrow> xs = (as @ u # bs)
  \<Longrightarrow> [v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us
  \<Longrightarrow> set zs \<inter> set xs \<subseteq> {u} \<union> set as
  \<Longrightarrow> [v \<leftarrow> zs@bs. v \<in> set us] = us"
proof -
  assume vors: "distinct xs" "xs = (as @ u # bs)"
    "[v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us"
    "set zs \<inter> set xs \<subseteq> {u} \<union> set as"
  have "set ([v\<leftarrow>xs. v = u \<or> v \<in> set us]) \<subseteq> set xs" by auto
  with vors have "set (u # us) \<subseteq> set xs" by simp
  then have "set us \<subseteq> set xs" by simp
  with vors have "set zs \<inter> set us \<subseteq> set zs \<inter> insert u (set as \<union> set bs)" by auto
  with vors show ?thesis apply (rule_tac filter_distinct_at4) apply assumption+ by auto
qed

lemma filter_distinct_at6: "distinct xs \<Longrightarrow> xs = (as @ u # bs)
  \<Longrightarrow> [v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us
  \<Longrightarrow> set zs \<inter> set xs \<subseteq> {u} \<union> set as
  \<Longrightarrow> [v \<leftarrow> zs@bs. v \<in> set us] = us \<and> [v \<leftarrow> bs. v \<in> set us] = us"
proof -
  assume vors: "distinct xs" "xs = (as @ u # bs)"
    "[v \<leftarrow> xs. v = u \<or> v \<in> set us] = u # us"
    "set zs \<inter> set xs \<subseteq> {u} \<union> set as"
  then show ?thesis apply (rule_tac conjI)  apply (rule_tac filter_distinct_at5) apply assumption+
  apply (drule filter_distinct_at) apply assumption+ by auto
qed

lemma filter_distinct_at_special:
  "distinct xs \<Longrightarrow> xs = (as @ u # bs)
  \<Longrightarrow> [v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us
  \<Longrightarrow> set zs \<inter> set xs \<subseteq> {u} \<union> set as
  \<Longrightarrow> us = hd_us # tl_us
  \<Longrightarrow> [v \<leftarrow> zs@bs. v \<in> set us] = us \<and> hd_us \<in> set bs"
proof -
  assume vors: "distinct xs" "xs = (as @ u # bs)"
    "[v\<leftarrow>xs. v = u \<or> v \<in> set us] = u # us"
    "set zs \<inter> set xs \<subseteq> {u} \<union> set as"
    "us = hd_us # tl_us"
  then have "[v \<leftarrow> zs@bs. v \<in> set us] = us \<and> [v\<leftarrow>bs. v \<in> set us] = us"
    by (rule_tac filter_distinct_at6)
  with vors show ?thesis apply (rule_tac conjI) apply safe apply simp
    apply (subgoal_tac "set (hd_us # tl_us) \<subseteq> set bs") apply simp
    apply (subgoal_tac "set [v\<leftarrow>bs . v = hd_us \<or> v \<in> set tl_us] \<subseteq> set bs")  apply simp
    by (rule_tac filter_is_subset)
qed




(* später ggf. pre_splitFace eliminieren *)
(* nein, Elimination nicht sinnvoll *)
lemma pre_subdivFace'_Some1':
assumes pre_add: "pre_subdivFace' g f v' v n ((Some u) # vol)"
    and pre_fdg: "pre_splitFace g v u f ws"
    and fdg:  "f21 = fst (snd (splitFace g v u f ws))"
    and g': "g' =  snd (snd (splitFace g v u f ws))"
shows "pre_subdivFace' g' f21 v' u 0 vol"
proof (cases "vol = []")
  case True then show ?thesis using pre_add fdg pre_fdg
    apply(unfold pre_subdivFace'_def pre_splitFace_def)
    apply (simp add: splitFace_def split_face_def split_def del:distinct.simps)
    apply (rule conjI)
     apply(clarsimp)
     apply(rule before_between)
        apply(erule (5) rotate_before_vFrom)
     apply(erule not_sym)
    apply (clarsimp simp:between_distinct between_not_r1 between_not_r2)
    apply(blast dest:inbetween_inset)
    done
next
  case False
  with pre_add
  have "removeNones vol \<noteq> []" apply (cases "vol" rule: rev_exhaust) by (auto simp: pre_subdivFace'_def)
  then have removeNones_split: "removeNones vol = hd (removeNones vol) # tl (removeNones vol)" by auto


  from pre_add have dist: "distinct (removeNones ((Some u) # vol))" by (rule_tac pre_subdivFace'_distinct)

  from pre_add have v': "v' \<in> \<V> f" by (auto simp: pre_subdivFace'_def)
  hence "(vertices f) \<cong> (verticesFrom f v')" by (rule verticesFrom_congs)
  hence set_eq: "set (verticesFrom f v') = \<V> f"
     apply (rule_tac sym) by (rule congs_pres_nodes)

  from pre_fdg fdg have dist_f21: "distinct (vertices f21)" by auto

  from pre_add have pre_bet': "pre_between (verticesFrom f v') u v"
    apply (simp add: pre_between_def pre_subdivFace'_def)
    apply (elim conjE) apply (thin_tac "n = 0 \<longrightarrow> \<not> is_duplicateEdge g f v u")
    apply (thin_tac "v' = v \<and> 0 < n \<or> v' = v \<and> u \<noteq> last (verticesFrom f v') \<or> v' \<noteq> v")
    apply (auto simp add: before_def)
    apply (subgoal_tac "distinct (verticesFrom f v')")  apply simp
    apply (rule_tac verticesFrom_distinct) by auto

  with pre_add have pre_bet: "pre_between (vertices f) u v"
    apply (subgoal_tac "(vertices f) \<cong> (verticesFrom f v')")
     apply (simp add: pre_between_def pre_subdivFace'_def)
    by (auto dest: congs_pres_nodes intro: verticesFrom_congs simp: pre_subdivFace'_def)

   from pre_bet pre_add have bet_eq[simp]: "between (vertices f) u v = between (verticesFrom f v') u v"
    by (auto intro: verticesFrom_between simp: pre_subdivFace'_def)

  from fdg have f21_split_face: "f21 = snd (split_face f v u ws)"
    by (simp add: splitFace_def split_def)
  then have f21: "f21 = Face (u # between (vertices f) u v @ v # ws) Nonfinal"
    by (simp add: split_face_def)
  with pre_add pre_bet'
  have vert_f21: "vertices f21
   = u # snd (splitAt u (verticesFrom f v')) @ fst (splitAt v (verticesFrom f v')) @ v # ws"
    apply (drule_tac pre_between_symI)
    by (auto simp: pre_subdivFace'_def between_simp2 intro: pre_between_symI)

  moreover
  from pre_add have "v \<in> set (verticesFrom f v')" by (auto simp: pre_subdivFace'_def before_def)
  then have "verticesFrom f v' =
   fst (splitAt v (verticesFrom f v')) @ v # snd (splitAt v (verticesFrom f v'))"
   by (auto dest: splitAt_ram)
  then have m: "v' # tl (verticesFrom f v')
    =  fst (splitAt v (verticesFrom f v')) @ v # snd (splitAt v (verticesFrom f v'))"
    by (simp add: verticesFrom_split)

  then have vv': "v \<noteq> v' \<Longrightarrow> fst (splitAt v (verticesFrom f v'))
    = v' # tl (fst (splitAt v (verticesFrom f v')))"
   by (cases "fst (splitAt v (verticesFrom f v'))") auto

  ultimately have "v \<noteq> v' \<Longrightarrow> vertices f21
    = u # snd (splitAt u (verticesFrom f v')) @ v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws"
    by auto

  moreover
  with f21 have rule2: "v' \<in> \<V> f21" by auto
  with dist_f21 have dist_f21_v': "distinct (verticesFrom f21 v')" by auto

  ultimately have m1: "v \<noteq> v' \<Longrightarrow> verticesFrom f21 v'
     = v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws @ u # snd (splitAt u (verticesFrom f v'))"
    apply auto
    apply (subgoal_tac "snd (splitAt v' (vertices f21)) = tl (fst (splitAt v (verticesFrom f v'))) @ v # ws")
     apply (subgoal_tac "fst (splitAt v' (vertices f21)) = u # snd (splitAt u (verticesFrom f v'))")
      apply (subgoal_tac "verticesFrom f21 v' = v' # snd (splitAt v' (vertices f21)) @ fst (splitAt v' (vertices f21))")
       apply simp
      apply (intro verticesFrom_v dist_f21) apply force
     apply (subgoal_tac "distinct (vertices f21)") apply simp
     apply (rule_tac dist_f21)
    apply (subgoal_tac "distinct (vertices f21)") apply simp
    by (rule_tac dist_f21)

  from pre_add have dist_vf_v': "distinct (verticesFrom f v')" by (simp add: pre_subdivFace'_def)
  with  vert_f21 have m2: "v = v' \<Longrightarrow> verticesFrom f21 v' = v' # ws @ u # snd (splitAt u (verticesFrom f v'))"
    apply auto apply (intro verticesFrom_v dist_f21) by simp

  from pre_add have u: "u \<in> set (verticesFrom f v')" by (fastforce simp: pre_subdivFace'_def before_def)
  then have split_u: "verticesFrom f v'
    = fst (splitAt u (verticesFrom f v')) @ u # snd (splitAt u (verticesFrom f v'))"
    by (auto dest!: splitAt_ram)

  then have rule1': "[v \<leftarrow> snd (splitAt u (verticesFrom f v')) . v \<in> set (removeNones vol)] = removeNones vol"
  proof -
    from split_u have "v' # tl (verticesFrom f v')
       =  fst (splitAt u (verticesFrom f v')) @ u # snd (splitAt u (verticesFrom f v'))"
      by (simp add: verticesFrom_split)
    have "help": "set [] \<inter> set (verticesFrom f v') \<subseteq> {u} \<union> set (fst (splitAt u (verticesFrom f v')))" by auto
    from split_u  dist_vf_v'  pre_add
    have "[v \<leftarrow> [] @ snd (splitAt u (verticesFrom f v')) . v \<in> set (removeNones vol)] = removeNones vol"
      apply (rule_tac filter_distinct_at5) apply assumption+
      apply (simp add: pre_subdivFace'_def) by (rule "help")
    then show ?thesis by auto
  qed
  then have inSnd_u: "\<And> x. x \<in> set (removeNones vol) \<Longrightarrow> x \<in> set (snd (splitAt u (verticesFrom f v')))"
    apply (subgoal_tac "x \<in> set [v \<leftarrow> snd (splitAt u (verticesFrom f v')) . v \<in> set (removeNones vol)] \<Longrightarrow>
      x \<in> set (snd (splitAt u (verticesFrom f v')))")
    apply force apply (thin_tac "[v \<leftarrow> snd (splitAt u (verticesFrom f v')) . v \<in> set (removeNones vol)] = removeNones vol")
    by simp

  from split_u dist_vf_v' have notinFst_u: "\<And> x. x \<in> set (removeNones vol) \<Longrightarrow>
      x \<notin> set ((fst (splitAt u (verticesFrom f v'))) @ [u])" apply (drule_tac inSnd_u)
    apply (subgoal_tac "distinct ( fst (splitAt u (verticesFrom f v')) @ u # snd (splitAt u (verticesFrom f v')))")
    apply (thin_tac "verticesFrom f v'
       = fst (splitAt u (verticesFrom f v')) @ u # snd (splitAt u (verticesFrom f v'))")
    apply simp apply safe
    apply (subgoal_tac "x \<in> set (fst (splitAt u (verticesFrom f v'))) \<inter> set (snd (splitAt u (verticesFrom f v')))")
    apply simp
    apply (thin_tac "set (fst (splitAt u (verticesFrom f v'))) \<inter> set (snd (splitAt u (verticesFrom f v'))) = {}")
    apply simp
    by (simp only:)

  from rule2 v' have "\<And> a b. is_nextElem (vertices f) a b \<and> a \<in> set (removeNones vol) \<and> b \<in> set (removeNones vol)  \<Longrightarrow>
   is_nextElem (vertices f21) a b"
  proof -
    fix a b
    assume vors: "is_nextElem (vertices f) a b \<and> a \<in> set (removeNones vol) \<and> b \<in> set (removeNones vol)"
    define vor_u where "vor_u = fst (splitAt u (verticesFrom f v'))"
    define nach_u where "nach_u = snd (splitAt u (verticesFrom f v'))"
    from vors v' have "is_nextElem (verticesFrom f v') a b"  by (simp add: verticesFrom_is_nextElem)
    moreover
    from vors inSnd_u nach_u_def have "a \<in> set (nach_u)" by auto
    moreover
    from vors inSnd_u nach_u_def have "b \<in> set (nach_u)" by auto
    moreover
    from split_u vor_u_def nach_u_def have "verticesFrom f v' = vor_u @ u # nach_u" by auto
    moreover
    note dist_vf_v'
    ultimately have "is_sublist [a,b] (nach_u)" apply (simp add: is_nextElem_def split:if_split_asm)
      apply (subgoal_tac "b \<noteq> hd (vor_u @ u # nach_u)")
       apply simp
       apply (subgoal_tac "distinct (vor_u @ (u # nach_u))")
        apply (drule is_sublist_at5)
         apply simp
        apply simp
        apply (erule disjE)
         apply (drule is_sublist_in1)+
         apply (subgoal_tac "b \<in> set vor_u \<inter> set nach_u") apply simp
         apply (thin_tac "set vor_u \<inter> set nach_u = {}")
         apply simp
        apply (erule disjE)
         apply (subgoal_tac "distinct ([u] @ nach_u)")
          apply (drule is_sublist_at5)
           apply simp
          apply simp
          apply (erule disjE)
           apply simp
          apply simp
         apply simp
        apply (subgoal_tac "distinct (vor_u @ (u # nach_u))")
         apply (drule is_sublist_at5) apply simp
        apply (erule disjE)
         apply (drule is_sublist_in1)+
         apply simp
        apply (erule disjE)
         apply  (drule is_sublist_in1)+ apply simp
        apply simp
       apply simp
      apply simp
     apply (cases "vor_u") by auto

    with nach_u_def have "is_sublist [a,b] (snd (splitAt u (verticesFrom f v')))" by auto
    then have "is_sublist [a,b] (verticesFrom f21 v')"
      apply (cases "v = v'") apply (simp_all add: m1 m2)
      apply (subgoal_tac "is_sublist [a, b] ((v' # ws @ [u]) @ snd (splitAt u (verticesFrom f v')) @ [])")
      apply simp apply (rule is_sublist_add) apply simp
      apply (subgoal_tac "is_sublist [a, b]
       ((v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws @ [u]) @ (snd (splitAt u (verticesFrom f v'))) @ [])")
      apply simp apply (rule is_sublist_add) by simp
    with rule2 show "is_nextElem (vertices f) a b \<and> a \<in> set (removeNones vol) \<and> b \<in> set (removeNones vol)  \<Longrightarrow>
      is_nextElem (vertices f21) a b" apply (simp add: verticesFrom_is_nextElem) by (auto simp: is_nextElem_def)
  qed
  with pre_add dist_f21 have rule5':
     "\<And> a b. (a,b) \<in> edges f \<and> a \<in> set (removeNones vol) \<and> b \<in> set (removeNones vol) \<Longrightarrow> (a, b) \<in> edges f21"
    by (simp add:  is_nextElem_edges_eq pre_subdivFace'_def)


  have rule1: "[v\<leftarrow>verticesFrom f21 v' . v \<in> set (removeNones vol)]
    = removeNones vol \<and> hd (removeNones vol) \<in> set (snd (splitAt u (verticesFrom f v')))"
  proof (cases "v = v'")
    case True
    from split_u have "v' # tl (verticesFrom f v')
      =  fst (splitAt u (verticesFrom f v')) @ u # snd (splitAt u (verticesFrom f v'))"
      by (simp add: verticesFrom_split)
    then have "u \<noteq> v' \<Longrightarrow> fst (splitAt u (verticesFrom f v'))
      = v' # tl (fst (splitAt u (verticesFrom f v')))" by (cases "fst (splitAt u (verticesFrom f v'))") auto
    moreover
    have "v' \<in> set (v' # tl (fst (splitAt u (verticesFrom f v'))))" by simp
    ultimately have "u \<noteq> v' \<Longrightarrow> v' \<in> set (fst (splitAt u (verticesFrom f v')))" by simp
    moreover
    from pre_fdg have "set (v' # ws @ [u]) \<inter> set (verticesFrom f v') \<subseteq>  {v', u}"
      apply (simp add: set_eq)
      by (unfold pre_splitFace_def) auto
    ultimately have "help": "set (v' # ws @ [u]) \<inter> set (verticesFrom f v')
      \<subseteq> {u} \<union> set (fst (splitAt u (verticesFrom f v')))" apply (rule_tac subset_trans)
      apply assumption apply (cases "u = v'") by simp_all
    from split_u dist_vf_v' pre_add pre_fdg removeNones_split have
      "[v \<leftarrow> (v' # ws @ [u]) @ snd (splitAt u (verticesFrom f v')) . v \<in> set (removeNones vol)]
      = removeNones vol \<and> hd (removeNones vol) \<in> set (snd (splitAt u (verticesFrom f v')))"
      apply (rule_tac filter_distinct_at_special) apply assumption+
      apply (simp add: pre_subdivFace'_def) apply (rule "help") .
    with True m2 show ?thesis by auto
  next
    case False

    with m1 dist_f21_v' have ne_uv': "u \<noteq> v'" by auto
    define fst_u where "fst_u = fst (splitAt u (verticesFrom f v'))"
    define fst_v where "fst_v = fst (splitAt v (verticesFrom f v'))"

    from pre_add u dist_vf_v' have "v \<in> set (fst (splitAt u (verticesFrom f v')))"
      apply (rule_tac before_dist_r1) by (auto  simp: pre_subdivFace'_def)
    with fst_u_def have "fst_u = fst (splitAt v (fst (splitAt u (verticesFrom f v'))))
         @ v # snd (splitAt v (fst (splitAt u (verticesFrom f v'))))"
      by (auto dest: splitAt_ram)
    with pre_add fst_v_def pre_bet' have fst_u':"fst_u
      = fst_v @ v # snd (splitAt v (fst (splitAt u (verticesFrom f v'))))" by (simp add: pre_subdivFace'_def)

    from pre_fdg have "set (v # ws @ [u]) \<inter> set (verticesFrom f v') \<subseteq>  {v, u}" apply (simp add: set_eq)
      by (unfold pre_splitFace_def) auto

    with fst_u' have "set (v # ws @ [u]) \<inter> set (verticesFrom f v') \<subseteq> {u} \<union> set fst_u" by auto
    moreover
    from fst_u' have "set fst_v \<subseteq> set fst_u" by auto
    ultimately
    have "(set (v # ws @ [u]) \<union> set fst_v) \<inter> set (verticesFrom f v') \<subseteq> {u} \<union> set fst_u" by auto
    with fst_u_def fst_v_def
    have "set (fst (splitAt v (verticesFrom f v')) @ v # ws @ [u]) \<inter> set (verticesFrom f v')
      \<subseteq> {u} \<union> set (fst (splitAt u (verticesFrom f v')))" by auto
    moreover
    with False vv' have  "v' # tl (fst (splitAt v (verticesFrom f v')))
      = fst (splitAt v (verticesFrom f v'))" by auto
    ultimately have "set ((v' # tl (fst (splitAt v (verticesFrom f v')))) @ v # ws @ [u]) \<inter> set (verticesFrom f v')
      \<subseteq> {u} \<union> set (fst (splitAt u (verticesFrom f v')))"
     by (simp only:)
    then have "help": "set (v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws @ [u]) \<inter> set (verticesFrom f v')
      \<subseteq> {u} \<union> set (fst (splitAt u (verticesFrom f v')))" by auto


    from split_u dist_vf_v' pre_add pre_fdg removeNones_split have
      "[v \<leftarrow> (v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws @ [u])
          @ snd (splitAt u (verticesFrom f v')) . v \<in> set (removeNones vol)]
       = removeNones vol \<and> hd (removeNones vol) \<in> set (snd (splitAt u (verticesFrom f v')))"
      apply (rule_tac filter_distinct_at_special) apply assumption+
      apply (simp add: pre_subdivFace'_def) apply (rule "help") .
    with False m1 show ?thesis by auto
  qed


  from rule1 have "(hd (removeNones vol)) \<in> set (snd (splitAt u (verticesFrom f v')))" by auto
  with m1 m2  dist_f21_v' have rule3: "before (verticesFrom f21 v') u (hd (removeNones vol))"
  proof -
    assume hd_ram: "(hd (removeNones vol)) \<in> set (snd (splitAt u (verticesFrom f v')))"
    from m1 m2 dist_f21_v' have "distinct (snd (splitAt u (verticesFrom f v')))" apply (cases "v = v'")
      by auto
    moreover
    define z1 where "z1 = fst (splitAt (hd (removeNones vol)) (snd (splitAt u (verticesFrom f v'))))"
    define z2 where "z2 = snd (splitAt (hd (removeNones vol)) (snd (splitAt u (verticesFrom f v'))))"
    note z1_def z2_def hd_ram
    ultimately have "snd (splitAt u (verticesFrom f v')) = z1 @ (hd (removeNones vol)) # z2"
      by (auto intro: splitAt_ram)
    with m1 m2 show ?thesis apply (cases "v = v'") apply (auto simp: before_def)
      apply (intro exI )
      apply (subgoal_tac "v' # ws @ u # z1 @ hd (removeNones vol) # z2 = (v' # ws) @ u # z1 @ hd (removeNones vol) # z2")
      apply assumption apply simp
      apply (intro exI )
      apply (subgoal_tac "v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws @ u # z1 @ hd (removeNones vol) # z2 =
        (v' # tl (fst (splitAt v (verticesFrom f v'))) @ v # ws) @ u # z1 @ hd (removeNones vol) # z2")
      apply assumption by simp
  qed

  from rule1 have ne:"(hd (removeNones vol)) \<in> set (snd (splitAt u (verticesFrom f v')))" by auto
  with m1 m2  have "last (verticesFrom f21 v') = last (snd (splitAt u (verticesFrom f v')))"
    apply (cases "snd (splitAt u (verticesFrom f v'))" rule: rev_exhaust) apply simp_all
    apply (cases "v = v'") by simp_all
  moreover
  from ne have "last (fst (splitAt u (verticesFrom f v')) @ u # snd (splitAt u (verticesFrom f v')))
    = last (snd (splitAt u (verticesFrom f v')))" by auto
  moreover
  note split_u
  ultimately  have rule4: "last (verticesFrom f v') = last (verticesFrom f21 v')" by simp


  have l: "\<And> a b f v. v \<in> set (vertices f) \<Longrightarrow> is_nextElem (vertices f) a b = is_nextElem (verticesFrom f v) a b "
    apply (rule is_nextElem_congs_eq) by (rule verticesFrom_congs)

  define f12 where "f12 = fst (split_face f v u ws)"
  then have f12_fdg: "f12 = fst (splitFace g v u f ws)"
    by (simp add: splitFace_def split_def)

   from pre_bet pre_add have bet_eq2[simp]: "between (vertices f) v u = between (verticesFrom f v') v u"
     apply (drule_tac pre_between_symI)
     by (auto intro: verticesFrom_between simp: pre_subdivFace'_def)


  from f12_fdg have f12_split_face: "f12 = fst (split_face f v u ws)"
    by (simp add: splitFace_def split_def)
  then have f12: "f12 = Face (rev ws @ v # between (verticesFrom f v') v u @ [u]) Nonfinal"
    by (simp add: split_face_def)
  then have "vertices f12 = rev ws @ v # between (verticesFrom f v') v u @ [u]" by simp
  with pre_add pre_bet' have vert_f12: "vertices f12
     = rev ws @ v # snd (splitAt v (fst (splitAt u (verticesFrom f v')))) @ [u]"
    apply (subgoal_tac "between (verticesFrom f v') v u = fst (splitAt u (snd (splitAt v (verticesFrom f v'))))")
     apply (simp  add: pre_subdivFace'_def)
    apply (rule between_simp1)
     apply (simp add: pre_subdivFace'_def)
    apply (rule pre_between_symI) .
  with dist_f21_v' have removeNones_vol_not_f12: "\<And> x. x \<in> set (removeNones vol) \<Longrightarrow> x \<notin> set (vertices f12)"
    apply (frule_tac notinFst_u) apply (drule inSnd_u) apply simp
    apply (case_tac "v = v'") apply (simp add: m1 m2)
    apply (rule conjI) apply force
    apply (rule conjI) apply (rule ccontr)  apply simp
    apply (subgoal_tac "x \<in> set ws \<inter> set (snd (splitAt u (verticesFrom f v')))")
    apply simp apply (elim conjE)
    apply (thin_tac "set ws \<inter> set (snd (splitAt u (verticesFrom f v'))) = {}")
    apply simp
    apply force

    apply (simp add: m1 m2)
    apply (rule conjI) apply force
    apply (rule conjI) apply (rule ccontr) apply simp
    apply (subgoal_tac "x \<in> set ws \<inter> set (snd (splitAt u (verticesFrom f v')))")
    apply simp apply (elim conjE)
    apply (thin_tac "set ws \<inter> set (snd (splitAt u (verticesFrom f v'))) = {}") apply simp
    by force

  from pre_fdg f12_split_face have dist_f12: "distinct (vertices f12)" by (auto intro: split_face_distinct1')

  then have removeNones_vol_edges_not_f12: "\<And> x y. x \<in> set (removeNones vol) \<Longrightarrow> (x,y) \<notin> edges f12" (* ? *)
    apply (drule_tac removeNones_vol_not_f12) by auto
  from dist_f12 have removeNones_vol_edges_not_f12': "\<And> x y. y \<in> set (removeNones vol) \<Longrightarrow> (x,y) \<notin> edges f12"
    apply (drule_tac removeNones_vol_not_f12) by auto

  from f12_fdg pre_fdg g' fdg have face_set_eq: "\<F> g' \<union> {f} = {f12, f21} \<union> \<F> g"
    apply (rule_tac splitFace_faces_1)
    by (simp_all)

  have rule5'': "\<And> a b. (a,b) \<in> edges g' \<and> (a,b) \<notin> edges g
     \<and> a \<in> set (removeNones vol) \<and> b \<in> set (removeNones vol) \<Longrightarrow> (a, b) \<in> edges f21" (* ? *)
    apply (simp add: edges_graph_def) apply safe
    apply (case_tac "x = f") apply simp apply (rule rule5') apply safe
    apply (subgoal_tac "x \<in> \<F> g' \<union> {f}") apply (thin_tac "x \<noteq> f")
    apply (thin_tac "x \<in> set (faces g')") apply (simp only: add: face_set_eq)
    apply safe apply (drule removeNones_vol_edges_not_f12) by auto
 have rule5''': "\<And> a b. (a,b) \<in> edges g' \<and> (a,b) \<notin> edges g
     \<and> a \<in> set (removeNones vol) \<and> b \<in> set (removeNones vol) \<Longrightarrow> (a, b) \<in> edges f21" (* ? *)

    apply (simp add: edges_graph_def) apply safe
    apply (case_tac "x = f") apply simp apply (rule rule5') apply safe
    apply (subgoal_tac "x \<in> \<F> g' \<union> {f}") apply (thin_tac "x \<noteq> f")
    apply (thin_tac "x \<in> \<F> g'") apply (simp only: add: face_set_eq)
    apply safe apply (drule removeNones_vol_edges_not_f12) by auto


 from pre_fdg fdg f12_fdg  g' have edges_g'1: "ws \<noteq> [] \<Longrightarrow> edges g' = edges g \<union> Edges ws \<union> Edges(rev ws) \<union>
   {(u, last ws), (hd ws, v), (v, hd ws), (last ws, u)}"
   apply (rule_tac splitFace_edges_g') apply simp
   apply (subgoal_tac "(f12, f21, g') = splitFace g v u f ws")  apply assumption by auto

 from pre_fdg fdg f12_fdg  g' have edges_g'2: "ws = [] \<Longrightarrow> edges g' = edges g \<union>
   {(v, u), (u, v)}"
   apply (rule_tac splitFace_edges_g'_vs) apply simp
   apply (subgoal_tac "(f12, f21, g') = splitFace g v u f []")  apply assumption by auto


 from f12_split_face f21_split_face have split: "(f12,f21) = split_face f v u ws" by simp


  from pre_add have "\<not> invalidVertexList g f vol"
    by (auto simp: pre_subdivFace'_def dest: invalidVertexList_shorten)
  then have rule5: "\<not> invalidVertexList g' f21 vol"

    apply (simp add: invalidVertexList_def)
    apply (intro allI impI)
    apply (case_tac "vol!i")  apply simp+
    apply (case_tac "vol!Suc i") apply simp+
    apply (subgoal_tac "\<not> is_duplicateEdge g f a aa")
     apply (thin_tac "\<forall>i<|vol| - Suc 0. \<not> (case vol ! i of None \<Rightarrow> False
        | Some a \<Rightarrow> case_option False (is_duplicateEdge g f a) (vol ! (i+1)))")
     apply (simp add: is_duplicateEdge_def)
     apply (subgoal_tac "a \<in> set (removeNones vol) \<and> aa \<in> set (removeNones vol)")
      apply (rule conjI)
       apply (rule impI)
       apply (case_tac "(a, aa) \<in> edges f")
        apply simp
        apply (subgoal_tac "pre_split_face f v u ws")
         apply (frule split_face_edges_or [OF split]) apply simp
         apply (simp add:  removeNones_vol_edges_not_f12)
        apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
       apply (case_tac "(aa, a) \<in> edges f")
        apply simp
        apply (subgoal_tac "pre_split_face f v u ws")
         apply (frule split_face_edges_or [OF split]) apply simp
         apply (simp add:  removeNones_vol_edges_not_f12)
        apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
       apply simp
       apply (case_tac "ws = []") apply (frule edges_g'2)  apply simp
        apply (subgoal_tac "pre_split_face f v u []")
         apply (subgoal_tac "(f12, f21) = split_face f v u ws")
          apply (case_tac "between (vertices f) u v = []")
           apply (frule split_face_edges_f21_bet_vs) apply simp apply simp
           apply simp
          apply (frule split_face_edges_f21_vs) apply simp apply simp apply simp
          apply (case_tac "a = v \<and> aa = u") apply simp apply simp
         apply (rule split)
        apply (subgoal_tac "pre_split_face f v u ws") apply simp
        apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
       apply (frule edges_g'1) apply simp
       apply (subgoal_tac "pre_split_face f v u ws")
        apply (subgoal_tac "(f12, f21) = split_face f v u ws")
         apply (case_tac "between (vertices f) u v = []")
          apply (frule split_face_edges_f21_bet) apply simp apply simp apply simp
          apply simp
          apply (case_tac "a = u \<and> aa = last ws") apply simp apply simp
          apply (case_tac "a = hd ws \<and> aa = v") apply simp apply simp
          apply (case_tac "a = v \<and> aa = hd ws") apply simp apply simp
          apply (case_tac "a = last ws \<and> aa = u") apply simp apply simp
          apply (case_tac "(a, aa) \<in> Edges ws") apply simp
          apply simp
         apply (frule split_face_edges_f21) apply simp apply simp apply simp apply simp
         apply (force)
        apply (rule split)
       apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
      apply (rule impI)
      apply (case_tac "(aa,a) \<in> edges f") apply simp
       apply (subgoal_tac "pre_split_face f v u ws")
        apply (frule split_face_edges_or [OF split]) apply simp
        apply (simp add:  removeNones_vol_edges_not_f12)
       apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
      apply (case_tac "(a,aa) \<in> edges f") apply simp
       apply (subgoal_tac "pre_split_face f v u ws")
        apply (frule split_face_edges_or [OF split]) apply simp
        apply (simp add:  removeNones_vol_edges_not_f12)
       apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
      apply simp
      apply (case_tac "ws = []") apply (frule edges_g'2) apply simp
       apply (subgoal_tac "pre_split_face f v u []")
        apply (subgoal_tac "(f12, f21) = split_face f v u ws")
         apply (case_tac "between (vertices f) u v = []")
          apply (frule split_face_edges_f21_bet_vs) apply simp apply simp
          apply simp
         apply (frule split_face_edges_f21_vs) apply simp apply simp apply simp
         apply force
        apply (rule split)
       apply (subgoal_tac "pre_split_face f v u ws") apply simp
       apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
      apply (frule edges_g'1) apply simp
      apply (subgoal_tac "pre_split_face f v u ws")
       apply (subgoal_tac "(f12, f21) = split_face f v u ws")
        apply (case_tac "between (vertices f) u v = []")
         apply (frule split_face_edges_f21_bet) apply simp apply simp apply simp
         apply (force)
        apply (frule split_face_edges_f21) apply simp apply simp apply simp apply simp
        apply (force)
       apply (rule split)
      apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
     apply (rule conjI)
      apply (subgoal_tac "Some a \<in> set vol") apply (induct vol) apply simp apply force
      apply (subgoal_tac "vol ! i \<in> set vol") apply simp
      apply (rule nth_mem) apply arith
     apply (subgoal_tac "Some aa \<in> set vol") apply (induct vol) apply simp apply force
     apply (subgoal_tac "vol ! (Suc i) \<in> set vol") apply simp apply (rule nth_mem) apply arith
    by auto


  from pre_fdg dist_f21 v' have dists: "distinct (vertices f)"  "distinct (vertices f12)"
     "distinct (vertices f21)"  "v' \<in> \<V> f"
    apply auto defer
    apply (drule splitFace_distinct2) apply (simp add: f12_fdg)
    apply (unfold pre_splitFace_def) by simp
  with pre_fdg have edges_or: "\<And> a b. (a,b) \<in> edges f \<Longrightarrow> (a,b) \<in> edges f12 \<or> (a,b) \<in> edges f21"
    apply (rule_tac split_face_edges_or) apply (simp add: f12_split_face f21_split_face)
   by simp+

 from pre_fdg have dist_f: "distinct (vertices f)" apply (unfold pre_splitFace_def) by simp

(* lemma *)
 from g' have edges_g': "edges g'
    = (UN h:set(replace f [snd (split_face f v u ws)] (faces g)). edges h)
    \<union> edges (fst (split_face f v u ws))"
  by (auto simp add: splitFace_def split_def edges_graph_def)


(* lemma *)
 from pre_fdg edges_g' have edges_g'_or:
   "\<And> a b. (a,b) \<in> edges g' \<Longrightarrow>
    (a,b) \<in> edges g \<or> (a,b) \<in> edges f12 \<or> (a,b) \<in> edges f21"
   apply simp apply (case_tac "(a, b) \<in> edges (fst (split_face f v u ws))")
   apply (simp add:f12_split_face) apply simp
   apply (elim bexE) apply (simp add: f12_split_face) apply (case_tac "x \<in> \<F> g")
   apply (induct g) apply (simp  add: edges_graph_def) apply (rule disjI1)
   apply (rule bexI) apply simp apply simp
   apply (drule replace1) apply simp by (simp add: f21_split_face)

  have rule6: "0 < |vol| \<Longrightarrow> \<not> invalidVertexList g f (Some u # vol) \<Longrightarrow>
    (\<exists>y. hd vol = Some y) \<longrightarrow> \<not> is_duplicateEdge g' f21 u (the (hd vol))"

    apply (rule impI)
    apply (erule exE) apply simp apply (case_tac vol) apply simp+
    apply (simp add: invalidVertexList_def) apply (erule allE) apply (erule impE) apply force
    apply (simp)
    apply (subgoal_tac "y \<notin> \<V> f12") defer apply (rule removeNones_vol_not_f12) apply simp
    apply (simp add: is_duplicateEdge_def)
    apply (subgoal_tac "y \<in> set (removeNones vol)")
     apply (rule conjI)
      apply (rule impI)
      apply (case_tac "(u, y) \<in> edges f") apply simp
       apply (subgoal_tac "pre_split_face f v u ws")
        apply (frule split_face_edges_or [OF split]) apply simp
        apply (simp add:  removeNones_vol_edges_not_f12')
       apply (rule pre_splitFace_pre_split_face) apply simp  apply (rule pre_fdg)
      apply (case_tac "(y, u) \<in> edges f") apply simp
       apply (subgoal_tac "pre_split_face f v u ws")
        apply (frule split_face_edges_or [OF split]) apply simp
        apply (simp add:  removeNones_vol_edges_not_f12)
       apply (rule pre_splitFace_pre_split_face) apply simp  apply (rule pre_fdg)
      apply simp
      apply (case_tac "ws = []") apply (frule edges_g'2)  apply simp
       apply (subgoal_tac "pre_split_face f v u []")
        apply (subgoal_tac "(f12, f21) = split_face f v u ws")
         apply (case_tac "between (vertices f) u v = []")
          apply (frule split_face_edges_f21_bet_vs) apply simp apply simp apply simp
         apply (frule split_face_edges_f21_vs) apply simp apply simp apply simp
         apply force
        apply (rule split)
       apply (subgoal_tac "pre_split_face f v u ws") apply simp
       apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
      apply (frule edges_g'1) apply simp
      apply (subgoal_tac "pre_split_face f v u ws")
       apply (subgoal_tac "(f12, f21) = split_face f v u ws")
        apply (case_tac "between (vertices f) u v = []")
         apply (frule split_face_edges_f21_bet) apply simp apply simp apply simp
         apply (force)
        apply (frule split_face_edges_f21) apply simp apply simp apply simp apply simp
        apply (force)
       apply (rule split)
      apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
     apply (rule impI)
     apply (case_tac "(u, y) \<in> edges f") apply simp
     apply (subgoal_tac "pre_split_face f v u ws")
      apply (frule split_face_edges_or [OF split]) apply simp apply (simp add:  removeNones_vol_edges_not_f12')
      apply (rule pre_splitFace_pre_split_face) apply simp  apply (rule pre_fdg)
     apply (case_tac "(y, u) \<in> edges f") apply simp
      apply (subgoal_tac "pre_split_face f v u ws")
       apply (frule split_face_edges_or [OF split]) apply simp apply (simp add:  removeNones_vol_edges_not_f12)
      apply (rule pre_splitFace_pre_split_face) apply simp  apply (rule pre_fdg)
     apply simp
     apply (case_tac "ws = []") apply (frule edges_g'2)  apply simp
      apply (subgoal_tac "pre_split_face f v u []")
       apply (subgoal_tac "(f12, f21) = split_face f v u ws")
        apply (case_tac "between (vertices f) u v = []")
         apply (frule split_face_edges_f21_bet_vs) apply simp apply simp
         apply simp
        apply (frule split_face_edges_f21_vs) apply simp apply simp apply simp
        apply force
       apply (rule split)
      apply (subgoal_tac "pre_split_face f v u ws") apply simp
      apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
     apply (frule edges_g'1) apply simp
     apply (subgoal_tac "pre_split_face f v u ws")
      apply (subgoal_tac "(f12, f21) = split_face f v u ws")
       apply (case_tac "between (vertices f) u v = []")
        apply (frule split_face_edges_f21_bet) apply simp apply simp apply simp
        apply (force)
       apply (frule split_face_edges_f21) apply simp apply simp apply simp apply simp
       apply (force)
      apply (rule split)
     apply (rule pre_splitFace_pre_split_face) apply (rule pre_fdg)
    by simp
  have u21: "u \<in> \<V> f21" by(simp add:f21)
  from fdg have "\<not> final f21"
    by(simp add:splitFace_def split_face_def split_def)
  with pre_add rule1 rule2 rule3 rule4 rule5 rule6 dist_f21 False dist u21
  show ?thesis by (simp_all add: pre_subdivFace'_def l)
qed


lemma before_filter: "\<And>  ys. filter P xs = ys \<Longrightarrow> distinct xs \<Longrightarrow> before ys  u v \<Longrightarrow> before xs u v"
  apply (subgoal_tac "P u")
  apply (subgoal_tac "P v")
  apply (subgoal_tac "pre_between xs u v")
  apply (rule ccontr) apply (simp add: before_xor)
  apply (subgoal_tac "before ys v u")
  apply (subgoal_tac "\<not> before ys v u")
  apply simp
  apply (rule before_dist_not1) apply force apply simp
  apply (simp add: before_def) apply (elim exE) apply simp
  apply (subgoal_tac "a @ u # b @ v # c = filter P aa @ v # filter P ba @ u # filter P ca")
  apply (intro exI) apply assumption
  apply simp
  apply (subgoal_tac "u \<in> set ys \<and> v \<in> set ys \<and> u \<noteq> v") apply (simp add: pre_between_def) apply force
  apply (subgoal_tac "distinct ys")
  apply (simp add: before_def) apply (elim exE) apply simp
  apply force
  apply (subgoal_tac "v \<in> set (filter P xs)") apply force
  apply (simp add: before_def) apply (elim exE) apply simp
  apply (subgoal_tac "u \<in> set (filter P xs)") apply force
  apply (simp add: before_def) apply (elim exE) by simp


lemma pre_subdivFace'_Some2: "pre_subdivFace' g f v' v 0 ((Some u) # vol) \<Longrightarrow> pre_subdivFace' g f v' u 0 vol"
apply (cases "vol = []")
 apply (simp add: pre_subdivFace'_def)
  apply (cases "u = v'") apply simp
 apply(rule verticesFrom_in')
  apply(rule last_in_set)
  apply(simp add:verticesFrom_Def)
 apply clarsimp
apply (simp add: pre_subdivFace'_def)
apply (elim conjE)
apply (thin_tac "v' = v \<and> u \<noteq> last (verticesFrom f v') \<or> v' \<noteq> v")
apply auto
    apply(rule verticesFrom_in'[where v = v'])
     apply(clarsimp simp:before_def)
    apply simp
   apply (rule ovl_shorten) apply simp
   apply (subgoal_tac "[v \<leftarrow> verticesFrom f v' . v \<in> set (removeNones ((Some u) # vol))] = removeNones ((Some u) # vol)")
    apply assumption
   apply simp
  apply (rule before_filter)
    apply assumption
   apply simp
  apply (simp add: before_def)
  apply (intro exI)
  apply (subgoal_tac "u # removeNones vol = [] @ u # [] @ hd (removeNones vol) # tl (removeNones vol)") apply assumption
  apply simp
  apply (subgoal_tac "removeNones vol \<noteq> []") apply simp
  apply (cases vol rule: rev_exhaust) apply simp_all
 apply (simp add: invalidVertexList_shorten)
apply (simp add: is_duplicateEdge_def)
apply (case_tac "vol") apply simp
apply simp
apply (simp add: invalidVertexList_def)
apply (elim allE)
apply (rotate_tac -1)
apply (erule impE)
 apply (subgoal_tac "0 < Suc |list|")
  apply assumption
 apply simp
apply simp
by (simp add: is_duplicateEdge_def)

lemma pre_subdivFace'_preFaceDiv: "pre_subdivFace' g f v' v n ((Some u) # vol)
  \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> (f \<bullet> v = u \<longrightarrow> n \<noteq> 0) \<Longrightarrow> \<V> f \<subseteq> \<V> g
  \<Longrightarrow> pre_splitFace g v u f [countVertices g ..< countVertices g + n]"
proof -
  assume pre_add: "pre_subdivFace' g f v' v n ((Some u) # vol)" and f: "f \<in> \<F> g"
  and nextVert: "(f \<bullet> v = u \<longrightarrow> n \<noteq> 0)" and subset: "\<V> f \<subseteq> \<V> g"
  have "distinct [countVertices g ..< countVertices g + n]" by (induct n) auto
  moreover
  have "\<V> g \<inter> set [countVertices g ..< countVertices g + n] = {}"
    apply (cases g) by auto
  with subset have "\<V> f \<inter> set [countVertices g ..< countVertices g + n] = {}" by auto
  moreover
  from pre_add have "\<V> f = set (verticesFrom f v')" apply (intro congs_pres_nodes verticesFrom_congs)
    by (simp add: pre_subdivFace'_def)
  with pre_add have "help": "v \<in> \<V> f \<and> u \<in> \<V> f \<and> v \<noteq> u"
    apply (simp add: pre_subdivFace'_def before_def)
    apply (elim conjE exE)
    apply (subgoal_tac "distinct (verticesFrom f v')") apply force
    apply (rule verticesFrom_distinct) by simp_all
  moreover
  from "help" pre_add nextVert have help1: "is_nextElem (vertices f) v u \<Longrightarrow> 0 < n" apply auto
    apply (simp add: nextVertex_def)
    by (simp add: nextElem_is_nextElem pre_subdivFace'_def)
  moreover
 have help2: "before (verticesFrom f v') v u \<Longrightarrow> distinct (verticesFrom f v') \<Longrightarrow> v \<noteq> v' \<Longrightarrow> \<not> is_nextElem (verticesFrom f v') u v"
   apply (simp add: before_def is_nextElem_def verticesFrom_hd is_sublist_def) apply safe
   apply (frule dist_at)
   apply simp
   apply (thin_tac "verticesFrom f v' = a @ v # b @ u # c")
   apply (subgoal_tac "verticesFrom f v' = (as @ [u]) @ v # bs") apply assumption
   apply simp apply (subgoal_tac "distinct (a @ v # b @ u # c)") apply force by simp
  note pre_add f
  moreover(*
  have "\<And> m. {k. k < m} \<inter> {k. m \<le> k \<and> k < (m + n)} = {}" by auto
  moreover*)

  from pre_add f help2 help1 "help" have "[countVertices g..<countVertices g + n] = [] \<Longrightarrow> (v, u) \<notin> edges f \<and> (u, v) \<notin> edges f"
    apply (cases "0 < n") apply (induct g) apply simp+
    apply (simp add: pre_subdivFace'_def)
    apply (rule conjI) apply force
    apply (simp split: if_split_asm)
     apply (rule ccontr)  apply simp
     apply (subgoal_tac "v = v'") apply simp  apply (elim conjE) apply (simp only:)
     apply (rule verticesFrom_is_nextElem_last) apply force apply force
     apply (simp add: verticesFrom_is_nextElem [symmetric])
    apply (cases "v = v'") apply simp
     apply (subgoal_tac "v' \<in> \<V> f")
      apply (thin_tac "u \<in> \<V> f")

      apply (simp add: verticesFrom_is_nextElem)
      apply (rule ccontr) apply simp
      apply (subgoal_tac "v' \<in> \<V> f")
       apply (drule verticesFrom_is_nextElem_hd) apply simp+

    apply (elim conjE) apply (drule help2)
      apply simp apply simp
    apply (subgoal_tac "is_nextElem (vertices f) u v = is_nextElem (verticesFrom f v') u v")
     apply simp
    apply (rule verticesFrom_is_nextElem) by simp
  ultimately

  show ?thesis
    apply (simp add: pre_subdivFace'_def)
    apply (unfold pre_splitFace_def)
    apply simp
    apply (cases "0 < n") apply (induct g) apply (simp add: ivl_disj_int)
    apply (auto simp: invalidVertexList_def is_duplicateEdge_def)
    done
qed


lemma pre_subdivFace'_Some1:
  "pre_subdivFace' g f v' v n ((Some u) # vol)
  \<Longrightarrow> f \<in> \<F> g \<Longrightarrow> (f \<bullet> v = u \<longrightarrow> n \<noteq> 0) \<Longrightarrow> \<V> f \<subseteq> \<V> g
  \<Longrightarrow> f21 = fst (snd (splitFace g v u f [countVertices g ..< countVertices g + n]))
  \<Longrightarrow> g' =  snd (snd (splitFace g v u f [countVertices g ..< countVertices g + n]))
  \<Longrightarrow> pre_subdivFace' g' f21 v' u 0 vol"
  apply (subgoal_tac "pre_splitFace g v u f [countVertices g ..< countVertices g + n]")
   apply (rule pre_subdivFace'_Some1') apply assumption+
  apply (simp)
  apply (rule pre_subdivFace'_preFaceDiv)
  by auto

end
