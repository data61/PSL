(*  Author: Dmitriy Traytel *)

section "Equivalence Framework"

(*<*)
theory Automaton
imports
  "HOL-Library.While_Combinator"
  Coinductive_Languages.Coinductive_Language
begin
(*>*)

coinductive rel_language where
  "\<lbrakk>\<oo> L = \<oo> K; \<And>a b. R a b \<Longrightarrow> rel_language R (\<dd> L a) (\<dd> K b)\<rbrakk> \<Longrightarrow> rel_language R L K"

declare rel_language.coinduct[consumes 1, case_names Lang, coinduct pred]

lemma rel_language_alt:
  "rel_language R L K = rel_fun (list_all2 R) (=) (in_language L) (in_language K)"
unfolding rel_fun_def proof (rule iffI, safe del: iffI)
  fix xs ys
  assume "list_all2 R xs ys" "rel_language R L K"
  then show "in_language L xs = in_language K ys"
    by (induct xs ys arbitrary: L K) (auto del: iffI elim: rel_language.cases)
next
  assume "\<forall>xs ys. list_all2 R xs ys \<longrightarrow> in_language L xs = in_language K ys"
  then show "rel_language R L K" by (coinduction arbitrary: L K) (auto dest: spec2)
qed

lemma rel_language_eq: "rel_language (=) = (=)"
  unfolding rel_language_alt[abs_def] list.rel_eq fun.rel_eq
  by (subst (2) fun_eq_iff)+
    (auto intro: box_equals[OF _ to_language_in_language to_language_in_language])

abbreviation "\<dd>s \<equiv> fold (\<lambda>a L. \<dd> L a)"

lemma in_language_\<dd>s: "in_language (\<dd>s w L) v \<longleftrightarrow> in_language L (w @ v)"
  by (induct w arbitrary: L) simp_all

lemma \<oo>_\<dd>s: "\<oo> (\<dd>s w L) \<longleftrightarrow> in_language L w"
  by (induct w arbitrary: L) auto

lemma in_language_to_language[simp]: "in_language (to_language L) w \<longleftrightarrow> w \<in> L"
  by (metis in_language_to_language mem_Collect_eq)

lemma rtrancl_fold_product:
shows "{((r, s), (f a r, g b s)) | a b r s. a \<in> A \<and> b \<in> B \<and> R a b}^* =
       {((r, s), (fold f w1 r, fold g w2 s)) | w1 w2 r s. w1 \<in> lists A \<and> w2 \<in> lists B \<and> list_all2 R w1 w2}"
  (is "?L = ?R")
proof-
  { fix r s r' s'
    have "((r, s), (r', s')) : ?L \<Longrightarrow> ((r, s), (r', s')) \<in> ?R"
    proof(induction rule: converse_rtrancl_induct2)
      case refl show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
  }
  hence "\<And>x. x \<in> ?L \<Longrightarrow> x \<in> ?R" by force
  moreover
  { fix r s r' s'
    { fix w1 w2 assume "list_all2 R w1 w2" "w1 \<in> lists A" "w2 \<in> lists B"
      then have "((r, s), fold f w1 r, fold g w2 s) \<in> ?L"
      proof(induction w1 w2 arbitrary: r s)
        case Nil show ?case by simp
      next
        case Cons thus ?case by (force elim!: converse_rtrancl_into_rtrancl[rotated])
      qed
    }
    hence "((r, s), (r', s')) \<in> ?R \<Longrightarrow> ((r, s), (r', s')) \<in> ?L" by auto
  }
  hence "\<And>x. x \<in> ?R \<Longrightarrow> x \<in> ?L" by blast
  ultimately show ?thesis by blast
qed

lemma rtrancl_fold_product1:
shows "{(r, s). \<exists>a \<in> A. s = f a r}^* = {(r, s). \<exists>a \<in> lists A. s = fold f a r}" (is "?L = ?R")
proof-
  { fix r s
    have "(r, s) \<in> ?L \<Longrightarrow> (r, s) \<in> ?R"
    proof(induction rule: converse_rtrancl_induct)
      case base show ?case by(force intro!: fold_simps(1)[symmetric])
    next
      case step thus ?case by(force intro!: fold_simps(2)[symmetric])
    qed
  } moreover
  { fix r s
    { fix w assume "w \<in> lists A"
      then have "(r, fold f w r) \<in> ?L"
      proof(induction w rule: rev_induct)
        case Nil show ?case by simp
      next
        case snoc thus ?case by (force elim!: rtrancl_into_rtrancl)
      qed
    } 
    hence "(r, s) \<in> ?R \<Longrightarrow> (r, s) \<in> ?L" by auto
  } ultimately show ?thesis by (auto 10 0)
qed

lemma lang_eq_ext_Nil_fold_Deriv:
  fixes K L A R
  assumes
    "\<And>w. in_language K w \<Longrightarrow> w \<in> lists A"
    "\<And>w. in_language L w \<Longrightarrow> w \<in> lists B"
    "\<And>a b. R a b \<Longrightarrow> a \<in> A \<longleftrightarrow> b \<in> B"
  defines "\<BB> \<equiv> {(\<dd>s w1 K, \<dd>s w2 L) | w1 w2. w1 \<in> lists A \<and> w2 \<in> lists B \<and> list_all2 R w1 w2}"
  shows "rel_language R K L \<longleftrightarrow> (\<forall>(K, L) \<in> \<BB>. \<oo> K \<longleftrightarrow> \<oo> L)"
proof
  assume "\<forall>(K, L)\<in>\<BB>. \<oo> K = \<oo> L"
  then show "rel_language R K L"
  unfolding \<BB>_def using assms(1,2)
  proof (coinduction arbitrary: K L)
    case (Lang K L)
    then have CIH: "\<And>K' L'. \<exists>w1 w2.
      K' = \<dd>s w1 K \<and> L' = \<dd>s w2 L \<and> w1 \<in> lists A \<and> w2 \<in> lists B \<and> list_all2 R w1 w2 \<Longrightarrow> \<oo> K' = \<oo> L'" and
      [dest]: "\<And>w. in_language K w \<Longrightarrow> w \<in> lists A" "\<And>w. in_language L w \<Longrightarrow> w \<in> lists B" 
      by blast+
    show ?case unfolding ex_simps simp_thms
    proof (safe del: iffI)
      show "\<oo> K = \<oo> L" by (intro CIH[OF exI[where x = "[]"]]) simp
    next
      fix x y w1 w2 assume "\<forall>x\<in>set w1. x \<in> A" "\<forall>x\<in>set w2. x \<in> B" "list_all2 R w1 w2" "R x y"
      then show "\<oo> (\<dd>s w1 (\<dd> K x)) = \<oo> (\<dd>s w2 (\<dd> L y))"
      proof (cases "x \<in> A \<and> y \<in> B")
        assume "\<not> (x \<in> A \<and> y \<in> B)"
        with assms(3)[OF \<open>R x y\<close>] show ?thesis
          by (auto simp: in_language_\<dd>s in_language.simps[symmetric] simp del: in_language.simps)
      qed (intro CIH exI[where x = "x # w1"] exI[where x = "y # w2"], auto)
    qed (auto simp add: in_language.simps[symmetric] simp del: in_language.simps)
  qed
qed (auto simp: \<BB>_def rel_language_alt rel_fun_def \<oo>_\<dd>s)

subsection \<open>Abstract Deterministic Automaton\<close>

locale DA =
fixes alphabet :: "'a list"
fixes init :: "'t \<Rightarrow> 's"
fixes delta :: "'a \<Rightarrow> 's \<Rightarrow> 's"
fixes accept :: "'s \<Rightarrow> bool"
fixes wellformed :: "'s \<Rightarrow> bool"
fixes Language :: "'s \<Rightarrow> 'a language"
fixes wf :: "'t \<Rightarrow> bool"
fixes Lang :: "'t \<Rightarrow> 'a language"
assumes distinct_alphabet: "distinct alphabet"
assumes Language_init: "wf t \<Longrightarrow> Language (init t) = Lang t"
assumes wellformed_init: "wf t \<Longrightarrow> wellformed (init t)"
assumes Language_alphabet: "\<lbrakk>wellformed s; in_language (Language s) w\<rbrakk> \<Longrightarrow> w \<in> lists (set alphabet)"
assumes wellformed_delta: "\<lbrakk>wellformed s; a \<in> set alphabet\<rbrakk> \<Longrightarrow> wellformed (delta a s)"
assumes Language_delta: "\<lbrakk>wellformed s; a \<in> set alphabet\<rbrakk> \<Longrightarrow> Language (delta a s) = \<dd> (Language s) a"
assumes accept_Language: "wellformed s \<Longrightarrow> accept s \<longleftrightarrow> \<oo> (Language s)"
begin

lemma this: "DA alphabet init delta accept wellformed Language wf Lang" by unfold_locales

lemma wellformed_deltas:
  "\<lbrakk>wellformed s; w \<in> lists (set alphabet)\<rbrakk> \<Longrightarrow> wellformed (fold delta w s)"
  by (induction w arbitrary: s) (auto simp add: Language_delta wellformed_delta)

lemma Language_deltas:
  "\<lbrakk>wellformed s; w \<in> lists (set alphabet)\<rbrakk> \<Longrightarrow> Language (fold delta w s) = \<dd>s w (Language s)"
  by (induction w arbitrary: s) (auto simp add: Language_delta wellformed_delta)

text\<open>Auxiliary functions:\<close>
definition reachable :: "'a list \<Rightarrow> 's \<Rightarrow> 's set" where
  "reachable as s = snd (the (rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. delta a s) as) s))"

definition automaton :: "'a list \<Rightarrow> 's \<Rightarrow> (('s * 'a) * 's) set" where
  "automaton as s =
    snd (the
    (let start = (([s], {s}), {});
         test = \<lambda>((ws, Z), A). ws \<noteq> [];
         step = \<lambda>((ws, Z), A).
           (let s = hd ws;
                new_edges = map (\<lambda>a. ((s, a), delta a s)) as;
                new = remdups (filter (\<lambda>ss. ss \<notin> Z) (map snd new_edges))
           in ((new @ tl ws, set new \<union> Z), set new_edges \<union> A))
    in while_option test step start))"

definition match :: "'s \<Rightarrow> 'a list \<Rightarrow> bool" where
  "match s w = accept (fold delta w s)"

lemma match_correct:
  assumes "wellformed s" "w \<in> lists (set alphabet)"
  shows "match s w \<longleftrightarrow> in_language (Language s) w"
  unfolding match_def accept_Language[OF wellformed_deltas[OF assms]] Language_deltas[OF assms] \<oo>_\<dd>s ..

end

locale DAs =
  M: DA alphabet1 init1 delta1 accept1 wellformed1 Language1 wf1 Lang1 +
  N: DA alphabet2 init2 delta2 accept2 wellformed2 Language2 wf2 Lang2
  for alphabet1 :: "'a1 list" and init1 :: "'t1 \<Rightarrow> 's1" and delta1 accept1 wellformed1 Language1 wf1 Lang1
  and alphabet2 :: "'a2 list" and init2 :: "'t2 \<Rightarrow> 's2" and delta2 accept2 wellformed2 Language2 wf2 Lang2 +
  fixes letter_eq :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool"
  assumes letter_eq: "\<And>a b. letter_eq a b \<Longrightarrow> a \<in> set alphabet1 \<longleftrightarrow> b \<in> set alphabet2"
begin

abbreviation step where
  "step \<equiv> (\<lambda>(p, q). map (\<lambda>(a, b). (delta1 a p, delta2 b q))
    (filter (case_prod letter_eq) (List.product alphabet1 alphabet2)))"

abbreviation closure :: "'s1 * 's2 \<Rightarrow> (('s1 * 's2) list * ('s1 * 's2) set) option" where
  "closure \<equiv> rtrancl_while (\<lambda>(p, q). accept1 p = accept2 q) step"

theorem closure_sound_complete:
assumes wf: "wf1 r" "wf2 s"
and result: "closure (init1 r, init2 s) = Some (ws, R)" (is "closure (?r, ?s) = _")
shows "ws = [] \<longleftrightarrow> rel_language letter_eq (Lang1 r) (Lang2 s)"
proof -
  from wf have wellformed: "wellformed1 ?r" "wellformed2 ?s"
    using M.wellformed_init N.wellformed_init by blast+
  note Language_alphabets[simp] =
    M.Language_alphabet[OF wellformed(1)] N.Language_alphabet[OF wellformed(2)]
  note Language_deltass = M.Language_deltas[OF wellformed(1)] N.Language_deltas[OF wellformed(2)]

  have bisim: "rel_language letter_eq (Language1 ?r) (Language2 ?s) =
    (\<forall>a b. (\<exists>w1 w2. a = \<dd>s w1 (Language1 ?r) \<and> b = \<dd>s w2 (Language2 ?s) \<and>
      w1 \<in> lists (set alphabet1) \<and> w2 \<in> lists (set alphabet2) \<and> list_all2 letter_eq w1 w2) \<longrightarrow>
    \<oo> a = \<oo> b)"
    by (subst lang_eq_ext_Nil_fold_Deriv) (auto dest: letter_eq)

  have leq: "rel_language letter_eq (Language1 ?r) (Language2 ?s) =
  (\<forall>(r', s') \<in> {((r, s), (delta1 a r, delta2 b s)) | a b r s.
    a \<in> set alphabet1 \<and> b \<in> set alphabet2 \<and> letter_eq a b}^* `` {(?r, ?s)}.
    accept1 r' = accept2 s')" using Language_deltass
      M.accept_Language[OF M.wellformed_deltas[OF wellformed(1)]]
      N.accept_Language[OF N.wellformed_deltas[OF wellformed(2)]]
      unfolding rtrancl_fold_product in_lists_conv_set bisim
      by (auto 10 0)
  have "{(x,y). y \<in> set (step x)} =
    {((r, s), (delta1 a r, delta2 b s)) | a b r s. a \<in> set alphabet1 \<and> b \<in> set alphabet2 \<and> letter_eq a b}"
    by auto
  with rtrancl_while_Some[OF result]
  have "(ws = []) = rel_language letter_eq (Language1 ?r) (Language2 ?s)"
    by (auto simp add: leq Ball_def split: if_splits)
  then show ?thesis unfolding M.Language_init[OF wf(1)] N.Language_init[OF wf(2)] .
qed

subsection \<open>The overall procedure\<close>

definition check_eqv :: "'t1 \<Rightarrow> 't2 \<Rightarrow> bool" where
"check_eqv r s = (wf1 r \<and> wf2 s \<and> (case closure (init1 r, init2 s) of Some([], _) \<Rightarrow> True | _ \<Rightarrow> False))"

lemma soundness: 
assumes "check_eqv r s" shows "rel_language letter_eq (Lang1 r) (Lang2 s)"
proof -
  obtain R where "wf1 r" "wf2 s" "closure (init1 r, init2 s) = Some([], R)"
    using assms by (auto simp: check_eqv_def Let_def split: option.splits list.splits)
  from closure_sound_complete[OF this] show "rel_language letter_eq (Lang1 r) (Lang2 s)" by simp
qed

(* completeness needs termination of closure, otherwise result could be None *)

end

subsection \<open>Abstract Deterministic Finite Automaton\<close>

locale DFA = DA +
assumes fin: "wellformed s \<Longrightarrow> finite {fold delta w s | w. w \<in> lists (set alphabet)}"
begin

lemma finite_rtrancl_delta_Image1:
  "wellformed r \<Longrightarrow> finite ({(r, s). \<exists>a \<in> set alphabet. s = delta a r}^* `` {r})"
  unfolding rtrancl_fold_product1 by (auto intro: finite_subset[OF _ fin])

lemma
  assumes "wellformed r" "set as \<subseteq> set alphabet"
  shows reachable: "reachable as r = {fold delta w r | w. w \<in> lists (set as)}"
  and finite_reachable: "finite (reachable as r)"
proof -
  obtain wsZ where *: "rtrancl_while (\<lambda>_. True) (\<lambda>s. map (\<lambda>a. delta a s) as) r = Some wsZ"
    using assms by (atomize_elim, intro rtrancl_while_finite_Some Image_mono rtrancl_mono
      finite_subset[OF _ finite_rtrancl_delta_Image1[of r]]) auto
  then show "reachable as r = {fold delta w r | w. w \<in> lists (set as)}"
    unfolding reachable_def by (cases wsZ)
      (auto dest!: rtrancl_while_Some split: if_splits simp: rtrancl_fold_product1 image_iff)
  then show "finite (reachable as r)" using assms by (force intro: finite_subset[OF _ fin])
qed

end

locale DFAs =
  M: DFA alphabet1 init1 delta1 accept1 wellformed1 Language1 wf1 Lang1 +
  N: DFA alphabet2 init2 delta2 accept2 wellformed2 Language2 wf2 Lang2
  for alphabet1 :: "'a1 list" and init1 :: "'t1 \<Rightarrow> 's1" and delta1 accept1 wellformed1 Language1 wf1 Lang1
  and alphabet2 :: "'a2 list" and init2 :: "'t2 \<Rightarrow> 's2" and delta2 accept2 wellformed2 Language2 wf2 Lang2 +
  fixes letter_eq :: "'a1 \<Rightarrow> 'a2 \<Rightarrow> bool"
  assumes letter_eq: "\<And>a b. letter_eq a b \<Longrightarrow> a \<in> set alphabet1 \<longleftrightarrow> b \<in> set alphabet2"
begin

interpretation DAs by unfold_locales (auto dest: letter_eq)

lemma finite_rtrancl_delta_Image:
  "\<lbrakk>wellformed1 r; wellformed2 s\<rbrakk> \<Longrightarrow>
  finite ({((r, s), (delta1 a r, delta2 b s))| a b r s.
    a \<in> set alphabet1 \<and> b \<in> set alphabet2 \<and> R a b}^* `` {(r, s)})"
  unfolding rtrancl_fold_product Image_singleton
  by (auto intro: finite_subset[OF _ finite_cartesian_product[OF M.fin N.fin]])

lemma "termination":
  assumes "wellformed1 r" "wellformed2 s"
  shows "\<exists>st. closure (r, s) = Some st" (is "\<exists>_. closure  ?i = _")
proof (rule rtrancl_while_finite_Some)
  show "finite ({(x, st). st \<in> set (step x)}\<^sup>* `` {?i})"
    by (rule finite_subset[OF Image_mono[OF rtrancl_mono]
      finite_rtrancl_delta_Image[OF assms, of letter_eq]]) auto
qed

lemma completeness: 
assumes "wf1 r" "wf2 s" "rel_language letter_eq (Lang1 r) (Lang2 s)" shows "check_eqv r s"
proof -
  obtain ws R where 1: "closure (init1 r, init2 s) = Some (ws, R)" using "termination"
    M.wellformed_init N.wellformed_init assms by fastforce
  with closure_sound_complete[OF _ _ this] assms
  show "check_eqv r s" by (simp add: check_eqv_def)
qed
  
end

sublocale DA < DAs
  alphabet init delta accept wellformed Language wf Lang
  alphabet init delta accept wellformed Language wf Lang "(=)"
  by unfold_locales auto

sublocale DFA < DFAs
  alphabet init delta accept wellformed Language wf Lang
  alphabet init delta accept wellformed Language wf Lang "(=)"
  by unfold_locales auto

lemma (in DA) step_alt: "step = (\<lambda>(p, q). map (\<lambda>a. (delta a p, delta a q)) alphabet)"
  using distinct_alphabet
proof (induct alphabet)
  case (Cons x xs)
  moreover
  { fix x :: 'a and xs ys :: "'a list"
    assume "x \<notin> set xs"
    then have "[(x, y)\<leftarrow>List.product xs (x # ys) . x = y] = [(x, y)\<leftarrow>List.product xs ys . x = y]"
      by (induct xs arbitrary: x) auto
  }
  moreover
  { fix x :: 'a and xs :: "'a list"
    assume "x \<notin> set xs"
    then have "[(x, y)\<leftarrow>map (Pair x) xs . x = y] = []"
      by (induct xs) auto
  }
  ultimately show ?case by (auto simp: fun_eq_iff)
qed simp

(*<*)
end
(*>*)
