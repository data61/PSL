(*<*)
theory Infinite_Proof_Soundness
imports Finite_Proof_Soundness "HOL-Library.BNF_Corec"
begin

(* Reference: A Generic Cyclic Theorem Prover
by James Brotherston, Nikos Gorogiannis, and Rasmus L. Petersen
*)
(*>*)

section \<open>Soundness of Infinite Proof Trees\<close>

context
begin

private definition "num P xs \<equiv> LEAST n. list_all (Not o P) (stake n xs) \<and> P (xs!!n)"

private lemma num:
  assumes ev: "ev (\<lambda>xs. P (shd xs)) xs"
  defines "n \<equiv> num P xs"
  shows
    "(list_all (Not o P) (stake n xs) \<and> P (xs!!n)) \<and>
 (\<forall>m. list_all (Not o P) (stake m xs) \<and> P (xs!!m) \<longrightarrow> n \<le> m)"
  unfolding n_def num_def
proof (intro conjI[OF LeastI_ex] allI impI Least_le)
  from ev show "\<exists>n. list_all (Not o P) (stake n xs) \<and> P (xs !! n)"
    by (induct rule: ev_induct_strong) (auto intro: exI[of _ 0] exI[of _ "Suc _"])
qed (simp_all add: o_def)

private lemma num_stl[simp]:
  assumes "ev (\<lambda>xs. P (shd xs)) xs" and "\<not> P (shd xs)"
  shows "num P xs = Suc (num P (stl xs))"
  unfolding num_def by (rule trans[OF Least_Suc[of _ "num P xs"]])
    (auto simp: num[OF assms(1)] assms(2))

corecursive decr0 where
  "decr0 Ord minSoFar js =
    (if \<not> (ev (\<lambda>js. (shd js, minSoFar) \<in> Ord \<and> shd js \<noteq> minSoFar)) js
     then undefined
     else if ((shd js, minSoFar) \<in> Ord \<and> shd js \<noteq> minSoFar)
          then shd js ## decr0 Ord (shd js) js
          else decr0 Ord minSoFar (stl js))"
  by (relation "measure (\<lambda>(Ord,m,js). num (\<lambda>j. (j, m) \<in> Ord \<and> j \<noteq> m) js)") auto

end

lemmas well_order_on_defs =
  well_order_on_def linear_order_on_def partial_order_on_def
  preorder_on_def trans_def antisym_def refl_on_def

lemma sdrop_length_shift[simp]:
  "sdrop (length xs) (xs @- s) = s"
  by (simp add: sdrop_shift)

lemma ev_iff_shift:
  "ev \<phi> xs \<longleftrightarrow> (\<exists>xl xs2. xs = xl @- xs2 \<and> \<phi> xs2)"
  by (meson ev.base ev_imp_shift ev_shift)

locale Infinite_Soundness = RuleSystem_Defs eff rules for
  eff :: "'rule \<Rightarrow> 'sequent \<Rightarrow> 'sequent fset \<Rightarrow> bool"
  and rules :: "'rule stream"
  +
  fixes "structure" :: "'structure set"
    and sat :: "'structure \<Rightarrow> 'sequent \<Rightarrow> bool"
    and \<delta> :: "'sequent \<Rightarrow> 'rule \<Rightarrow> 'sequent \<Rightarrow> ('marker \<times> bool \<times> 'marker) set"
    and Ord :: "'ord rel"
    and \<sigma> :: "'marker \<times> 'structure \<Rightarrow> 'ord"
  assumes
    Ord: "well_order Ord"
    and
    descent: (* The original paper has an error in stating this: quantifies existentially
  instead of universally over r *)
    "\<And>r s sl S.
      \<lbrakk>r \<in> R; eff r s sl; S \<in> structure; \<not> sat S s\<rbrakk>
      \<Longrightarrow>
      \<exists>s' S'.
        s' |\<in>| sl \<and> S' \<in> structure \<and> \<not> sat S' s' \<and>
        (\<forall>v v' b.
          (v,b,v') \<in> \<delta> s r s' \<longrightarrow>
             (\<sigma>(v',S'), \<sigma>(v,S)) \<in> Ord \<and> (b \<longrightarrow> \<sigma>(v',S') \<noteq> \<sigma>(v,S)))"

(* The descent property subsumes local_soundness: *)
sublocale Infinite_Soundness < Soundness where eff = eff and rules = rules
  and "structure" = "structure" and sat = sat
  by standard (blast dest: descent)

context Infinite_Soundness
begin

(* The notion of a trace of markers following a path: to make the original paper definition
into a rigorous one, we include the trace of "progressing bits" as well:  *)
coinductive follow :: "bool stream \<Rightarrow> 'marker stream \<Rightarrow> ('sequent,'rule)step stream \<Rightarrow> bool" where
  "\<lbrakk>M' = shd Ms; s' = fst (shd steps); (M,b,M') \<in> \<delta> s r s'; follow bs Ms steps\<rbrakk>
 \<Longrightarrow>
 follow (SCons b bs) (SCons M Ms) (SCons (s,r) steps)"

(* Now infinite progress simply means "always eventually the bit is True": *)
definition infDecr :: "bool stream \<Rightarrow> bool" where
  "infDecr \<equiv> alw (ev (\<lambda>bs. shd bs))"

(* Good trees: *)
definition good :: "('sequent,'rule)dtree \<Rightarrow> bool" where
  "good t \<equiv> \<forall>steps.
  ipath t steps
  \<longrightarrow>
  ev (\<lambda>steps'. \<exists>bs Ms. follow bs Ms steps' \<and> infDecr bs) steps"
(* Note the mixture of temporal connectives and standard HOL quantifiers:
an advantage of the shallow embedding of LTL *)

(* Trivially, finite trees are particular cases of good trees, since they
have no infinite paths: *)
lemma tfinite_good: "tfinite t \<Longrightarrow> good t"
  using ftree_no_ipath unfolding good_def by auto

context
  fixes inv :: "'sequent \<times> 'a \<Rightarrow> bool"
    and pred :: "'sequent \<times> 'a \<Rightarrow> 'rule \<Rightarrow> 'sequent \<times> 'a \<Rightarrow> bool"
begin

primcorec konigDtree ::
  "('sequent,'rule) dtree \<Rightarrow> 'a \<Rightarrow> (('sequent,'rule) step \<times> 'a) stream" where
  "shd (konigDtree t a) = (root t, a)"
|"stl (konigDtree t a) =
  (let s = fst (root t); r = snd (root t);
   (s',a') = (SOME (s',a'). s' |\<in>| fimage (fst o root) (cont t) \<and> pred (s,a) r (s',a') \<and> inv (s',a'));
   t' = (SOME t'. t' |\<in>| cont t \<and> s' = fst (root t'))
   in konigDtree t' a'
  )"

lemma stl_konigDtree:
  fixes t defines "s \<equiv> fst (root t)" and "r \<equiv> snd (root t)"
  assumes s': "s' |\<in>| fimage (fst o root) (cont t)"  and "pred (s,a) r (s',a'')" and "inv (s',a'')"
  shows "\<exists>t' a'. t' |\<in>| cont t \<and> pred (s,a) r (fst (root t'),a') \<and> inv (fst (root t'),a')
  \<and> stl (konigDtree t a) = konigDtree t' a'"
proof-
  define P where "P \<equiv> \<lambda>(s',a'). s' |\<in>| fimage (fst o root) (cont t) \<and> pred (s,a) r (s',a') \<and> inv (s',a')"
  define s'a' where "s'a' \<equiv> SOME (s',a'). P (s',a')"  let ?s' = "fst s'a'"  let ?a' = "snd s'a'"
  define t' where "t' \<equiv> SOME (t'::('sequent,'rule)dtree). t' |\<in>| cont t \<and> ?s' = fst (root t')"
  have "P (s',a'')" using assms unfolding P_def by auto
  hence P: "P (?s',?a')" using someI[of P] unfolding s'a'_def by auto
  hence "\<exists>t'. t' |\<in>| cont t \<and> ?s' = fst (root t')" unfolding P_def by auto
  hence t': "t' |\<in>| cont t" and s': "?s' = fst (root t')"
    using someI_ex[of "\<lambda>t'. t' |\<in>| cont t \<and> ?s' = fst (root t')"] unfolding t'_def by auto
  show ?thesis using t' P s' assms P_def s'a'_def t'_def by (intro exI[of _ t'] exI[of _ ?a']) auto
qed

declare konigDtree.simps(2)[simp del]

lemma konigDtree:
  assumes 1: "\<And>r s sl a.
  \<lbrakk>r \<in> R; eff r s sl; inv (s,a)\<rbrakk> \<Longrightarrow>
  \<exists>s' a'. s' |\<in>| sl \<and> inv (s',a') \<and> pred (s,a) r (s',a')"
    and 2: "wf t" "inv (fst (root t), a)"
  shows
    "alw (\<lambda>stepas.
        let ((s,r),a) = shd stepas; ((s',_),a') = shd (stl stepas) in
          inv (s,a) \<and> pred (s,a) r (s',a'))
     (konigDtree t a)"
  using assms proof (coinduction arbitrary: t a)
  case (alw t a)
  then obtain s' a' where "s' |\<in>| (fst \<circ> root) |`| cont t" "inv (s', a')"
    "pred (fst (root t), a) (snd (root t)) (s', a')"
    by (auto elim!: wf.cases dest!: spec[of _ "snd (root t)"] spec[of _ "fst (root t)"]
        spec[of _ "(fst \<circ> root) |`| cont t"] spec[of _ a], fastforce)
  with alw stl_konigDtree[of s' t a a'] show ?case
    by (auto split: prod.splits elim!: wf.cases) fastforce
qed

lemma konigDtree_ipath:
  assumes "\<And>r s sl a.
  \<lbrakk>r \<in> R; eff r s sl; inv (s,a)\<rbrakk> \<Longrightarrow>
  \<exists>s' a'. s' |\<in>| sl \<and> inv (s',a') \<and> pred (s,a) r (s',a')"
    and "wf t" and "inv (fst (root t), a)"
  shows "ipath t (smap fst (konigDtree t a))"
  using assms proof (coinduction arbitrary: t a)
  case (ipath t a)
  then obtain s' a' where "s' |\<in>| (fst \<circ> root) |`| cont t" "inv (s', a')"
    "pred (fst (root t), a) (snd (root t)) (s', a')"
    by (auto elim!: wf.cases dest!: spec[of _ "snd (root t)"] spec[of _ "fst (root t)"]
        spec[of _ "(fst \<circ> root) |`| cont t"] spec[of _ a], fastforce)
  with ipath stl_konigDtree[of s' t a a'] show ?case
    by (auto split: prod.splits elim!: wf.cases) force
qed

end (* context *)

lemma follow_stl_smap_fst[simp]:
  "follow bs Ms (smap fst stepSs) \<Longrightarrow>
   follow (stl bs) (stl Ms) (smap fst (stl stepSs))"
  by (erule follow.cases) (auto simp del: stream.map_sel simp add: stream.map_sel[symmetric])

lemma epath_stl_smap_fst[simp]:
  "epath (smap fst stepSs) \<Longrightarrow>
   epath (smap fst (stl stepSs))"
  by (erule epath.cases) (auto simp del: stream.map_sel simp add: stream.map_sel[symmetric])

lemma infDecr_tl[simp]: "infDecr bs \<Longrightarrow> infDecr (stl bs)"
  unfolding infDecr_def by auto

(* Proof of the main theorem: *)
fun descent where "descent (s,S) r (s',S') =
 (\<forall>v v' b.
    (v,b,v') \<in> \<delta> s r s' \<longrightarrow>
    (\<sigma>(v',S'), \<sigma>(v,S)) \<in> Ord \<and> (b \<longrightarrow> \<sigma>(v',S') \<noteq> \<sigma>(v,S)))"

lemma descentE[elim]:
  assumes "descent (s,S) r (s',S')" and "(v,b,v') \<in> \<delta> s r s'"
  shows "(\<sigma>(v',S'), \<sigma>(v,S)) \<in> Ord \<and> (b \<longrightarrow> \<sigma>(v',S') \<noteq> \<sigma>(v,S))"
  using assms by auto

definition "konigDown \<equiv> konigDtree (\<lambda>(s,S). S \<in> structure \<and> \<not> sat S s) descent"

lemma konigDown:
  assumes "wf t" and "S \<in> structure" and "\<not> sat S (fst (root t))"
  shows
    "alw (\<lambda>stepSs. let ((s,r),S) = shd stepSs; ((s',_),S') = shd (stl stepSs) in
                    S \<in> structure \<and> \<not> sat S s \<and> descent (s,S) r (s',S'))
     (konigDown t S)"
  using konigDtree[of "\<lambda>(s,S). S \<in> structure \<and> \<not> sat S s" descent, unfolded konigDown_def[symmetric]]
  using assms descent by auto

lemma konigDown_ipath:
  assumes "wf t" and "S \<in> structure" and "\<not> sat S (fst (root t))"
  shows
    "ipath t (smap fst (konigDown t S))"
  using konigDtree_ipath[of "\<lambda>(s,S). S \<in> structure \<and> \<not> sat S s" descent, unfolded konigDown_def[symmetric]]
  using assms descent by auto

context
  fixes t S
  assumes w: "wf t" and t: "good t" and S: "S \<in> structure" "\<not> sat S (fst (root t))"
begin

lemma alw_ev_Ord:
  obtains ks where "alw (\<lambda>ks. (shd (stl ks), shd ks) \<in> Ord) ks"
    and "alw (ev (\<lambda>ks. shd (stl ks) \<noteq> shd ks)) ks"
proof-
  define P where "P \<equiv> \<lambda>stepSs. let ((s,r),S) = shd stepSs; ((s',_),S') = shd (stl stepSs) in
                      S \<in> structure \<and> \<not> sat S s \<and> descent (s,S) r (s',S')"
  have "alw P (konigDown t S)" using konigDown[OF w S] unfolding P_def by auto
  obtain srs steps bs Ms where 0: "smap fst (konigDown t S) = srs @- steps" and
    f: "follow bs Ms steps" and i: "infDecr bs"
    using konigDown_ipath[OF w S] t unfolding good_def ev_iff_shift by auto
  define stepSs where "stepSs = sdrop (length srs) (konigDown t S)"
  have steps: "steps = smap fst stepSs" unfolding stepSs_def sdrop_smap[symmetric] 0 by simp
  have e: "epath steps"
    using wf_ipath_epath[OF w konigDown_ipath[OF w S]] 0 epath_shift by simp
  have "alw P (konigDown t S)" using konigDown[OF w S] unfolding P_def by auto
  hence P: "alw P stepSs" using alw_sdrop unfolding stepSs_def by auto
  let ?ks = "smap \<sigma> (szip Ms (smap snd stepSs))"
  show ?thesis proof(rule that[of ?ks])
    show "alw (\<lambda>ks. (shd (stl ks), shd ks) \<in> Ord) ?ks"
      using e f P unfolding steps proof(coinduction arbitrary: bs Ms stepSs rule: alw_coinduct)
      case (alw bs Ms stepSs)
      let ?steps = "smap fst stepSs" let ?Ss = "smap snd stepSs"
      let ?MSs = "szip Ms (smap snd stepSs)"
      let ?s = "fst (shd ?steps)"  let ?s' = "fst (shd (stl ?steps))"
      let ?r = "snd (shd ?steps)"
      let ?S = "snd (shd stepSs)"  let ?S' = "snd (shd (stl stepSs))"
      let ?M = "shd Ms"  let ?M' = "shd (stl Ms)"  let ?b = "shd bs"
      have 1: "(?M, ?b, ?M') \<in> \<delta> ?s ?r ?s'"
        using \<open>follow bs Ms (smap fst stepSs)\<close> by (cases rule: follow.cases) auto
      have 2: "descent (?s,?S) ?r (?s',?S')"
        using \<open>alw P stepSs\<close> unfolding P_def by (cases rule: alw.cases) auto
      have "(\<sigma>(?M',?S'), \<sigma>(?M,?S)) \<in> Ord" using descentE[OF 2 1] by simp
      thus ?case by simp
    next
      case (stl bs Ms stepSs)
      thus ?case
        by (intro exI[of _ "stl bs"] exI[of _ "stl Ms"] exI[of _ "stl stepSs"])
          (auto elim: epath.cases)
    qed
  next
    show "alw (ev (\<lambda>ks. shd (stl ks) \<noteq> shd ks)) ?ks"
      using e f P i unfolding steps proof(coinduction arbitrary: bs Ms stepSs rule: alw_coinduct)
      case (alw bs Ms stepSs)
      let ?steps = "smap fst stepSs" let ?Ss = "smap snd stepSs"
      let ?MSs = "szip Ms (smap snd stepSs)"
      let ?s = "fst (shd ?steps)"  let ?s' = "fst (shd (stl ?steps))"
      let ?r = "snd (shd ?steps)"
      let ?S = "snd (shd stepSs)"  let ?S' = "snd (shd (stl stepSs))"
      let ?M = "shd Ms"  let ?M' = "shd (stl Ms)"  let ?b = "shd bs"
      have 1: "(?M, ?b, ?M') \<in> \<delta> ?s ?r ?s'"
        using \<open>follow bs Ms (smap fst stepSs)\<close> by (cases rule: follow.cases) auto
      have 2: "descent (?s,?S) ?r (?s',?S')"
        using \<open>alw P stepSs\<close> unfolding P_def by (cases rule: alw.cases) auto
      have "(\<sigma>(?M',?S'), \<sigma>(?M,?S)) \<in> Ord" using descentE[OF 2 1] by simp
      have "ev shd bs" using \<open>infDecr bs\<close> unfolding infDecr_def by auto
      thus ?case using \<open>epath ?steps\<close> \<open>follow bs Ms ?steps\<close> \<open>alw P stepSs\<close>
      proof (induction arbitrary: Ms stepSs)
        case (base bs Ms stepSs)
        let ?steps = "smap fst stepSs" let ?Ss = "smap snd stepSs"
        let ?MSs = "szip Ms (smap snd stepSs)"
        let ?s = "fst (shd ?steps)"  let ?s' = "fst (shd (stl ?steps))"
        let ?r = "snd (shd ?steps)"
        let ?S = "snd (shd stepSs)"  let ?S' = "snd (shd (stl stepSs))"
        let ?M = "shd Ms"  let ?M' = "shd (stl Ms)"  let ?b = "shd bs"
        have 1: "(?M, ?b, ?M') \<in> \<delta> ?s ?r ?s'"
          using \<open>follow bs Ms (smap fst stepSs)\<close> by (cases rule: follow.cases) auto
        have 2: "descent (?s,?S) ?r (?s',?S')"
          using \<open>alw P stepSs\<close> unfolding P_def by (cases rule: alw.cases) auto
        have "\<sigma>(?M',?S') \<noteq> \<sigma>(?M,?S)" using descentE[OF 2 1] \<open>shd bs\<close> by simp
        thus ?case by auto
      next
        case (step bs Ms stepSs)
        have "ev (\<lambda>ks. shd (stl ks) \<noteq> shd ks)
                  (smap \<sigma>
                  (szip (stl Ms) (smap snd (stl stepSs))))"
          using step(3-5) step(2)[of "stl stepSs" "stl Ms"] by auto
        thus ?case by auto
      qed
    next
      case (stl bs Ms stepSs)
      thus ?case
        by (intro exI[of _ "stl bs"] exI[of _ "stl Ms"] exI[of _ "stl stepSs"])
          (auto elim: epath.cases)
    qed
  qed
qed

definition
  "ks \<equiv> SOME ks.
        alw (\<lambda>ks. (shd (stl ks), shd ks) \<in> Ord) ks \<and>
        alw (ev (\<lambda>ks. shd (stl ks) \<noteq> shd ks)) ks"

lemma alw_ks: "alw (\<lambda>ks. (shd (stl ks), shd ks) \<in> Ord) ks"
  and alw_ev_ks: "alw (ev (\<lambda>ks. shd (stl ks) \<noteq> shd ks)) ks"
  unfolding ks_def using alw_ev_Ord someI_ex[of "\<lambda>ks.
        alw (\<lambda>ks. (shd (stl ks), shd ks) \<in> Ord) ks \<and>
        alw (ev (\<lambda>ks. shd (stl ks) \<noteq> shd ks)) ks"]
  by auto

abbreviation decr where "decr \<equiv> decr0 Ord"

lemmas decr_simps = decr0.code[of Ord]

context
  fixes js
  assumes a: "alw (\<lambda>js. (shd (stl js), shd js) \<in> Ord) js"
    and ae: "alw (ev (\<lambda>js. shd (stl js) \<noteq> shd js)) js"
begin

lemma decr_ev:
  assumes m: "(shd js, m) \<in> Ord"
  shows "ev (\<lambda>js. (shd js, m) \<in> Ord \<and> shd js \<noteq> m) js"
    (is "ev (\<lambda>js. ?\<phi> m js) js")
proof-
  have "ev (\<lambda>js. shd (stl js) \<noteq> shd js) js" using ae by auto
  thus ?thesis
    using a m proof induction
    case (base ls)
    hence "ev (?\<phi> (shd ls)) ls" by auto
    moreover have "\<And>js. ?\<phi> (shd ls) js \<Longrightarrow> ?\<phi> m js"
      using \<open>(shd ls, m) \<in> Ord\<close> Ord unfolding well_order_on_defs by blast
    ultimately show ?case using ev_mono[of "?\<phi> (shd ls)" _ "?\<phi> m"] by auto
  qed auto
qed

lemma decr_simps_diff[simp]:
  assumes m: "(shd js, m) \<in> Ord"
    and "shd js \<noteq> m"
  shows "decr m js = shd js ## decr (shd js) js"
  using decr_ev[OF m] assms by (subst decr_simps) simp

lemma decr_simps_eq[simp]:
  "decr (shd js) js = decr (shd js) (stl js)"
proof-
  have m: "(shd js, shd js) \<in> Ord" using Ord
    unfolding well_order_on_def linear_order_on_def partial_order_on_def
      preorder_on_def refl_on_def by auto
  show ?thesis using decr_ev[OF m] by (subst decr_simps) simp
qed

end (* context *)

lemma stl_decr:
  assumes a: "alw (\<lambda>js. (shd (stl js), shd js) \<in> Ord) js"
    and ae: "alw (ev (\<lambda>js. shd (stl js) \<noteq> shd js)) js"
    and m: "(shd js, m) \<in> Ord"
  shows
    "\<exists>js1 js2. js = js1 @- js2 \<and> set js1 \<subseteq> {m} \<and>
 (shd js2, m) \<in> Ord \<and> shd js2 \<noteq> m \<and>
  shd (decr m js) = shd js2 \<and> stl (decr m js) = decr (shd js2) js2"
    (is "\<exists>js1 js2. ?\<phi> js js1 js2")
  using decr_ev[OF assms] m a ae proof (induction rule: ev_induct_strong)
  case (base js)
  thus ?case by  (intro exI[of _ "[]"] exI[of _ js]) auto
next
  case (step js)
  then obtain js1 js2 where 1: "?\<phi> (stl js) js1 js2" and [simp]: "shd js = m" by auto
  thus ?case
    by (intro exI[of _ "shd js # js1"] exI[of _ js2],
      simp, metis (lifting) decr_simps_eq step(2,4,5,6) stream.collapse)
qed

corollary stl_decr_shd:
  assumes a: "alw (\<lambda>js. (shd (stl js), shd js) \<in> Ord) js" and
    ae: "alw (ev (\<lambda>js. shd (stl js) \<noteq> shd js)) js"
  shows
    "\<exists>js1 js2. js = js1 @- js2 \<and> set js1 \<subseteq> {shd js} \<and>
 (shd js2, shd js) \<in> Ord \<and> shd js2 \<noteq> shd js \<and>
  shd (decr (shd js) js) = shd js2 \<and> stl (decr (shd js) js) = decr (shd js2) js2"
  using Ord unfolding well_order_on_defs by (intro stl_decr[OF assms]) blast

lemma decr:
  assumes a: "alw (\<lambda>js. (shd (stl js), shd js) \<in> Ord) js" (is "?a js")
    and ae: "alw (ev (\<lambda>js. shd (stl js) \<noteq> shd js)) js" (is "?ae js")
  shows
    "alw (\<lambda>js. (shd (stl js), shd js) \<in> Ord \<and> shd (stl js) \<noteq> shd js) (decr (shd js) js)"
    (is "alw ?\<phi> _")
proof-
  let ?\<xi> = "\<lambda>ls js. ls = decr (shd js) js \<and> ?a js \<and> ?ae js"
  {fix ls assume "\<exists>js. ?\<xi> ls js"
    hence "alw ?\<phi> ls" proof(elim alw_coinduct)
      fix ls assume "\<exists>js. ?\<xi> ls js"
      then obtain js where 1: "?\<xi> ls js" by auto
      then obtain js1 js2 where js: "js = js1 @- js2 \<and> set js1 \<subseteq> {shd js} \<and>
       (shd js2, shd js) \<in> Ord \<and> shd js2 \<noteq> shd js \<and>
       shd ls = shd js2 \<and> stl ls = decr (shd js2) js2"
        using stl_decr_shd by blast
      then obtain js3 js4 where js2: "js2 = js3 @- js4 \<and> set js3 \<subseteq> {shd js2} \<and>
       (shd js4, shd js2) \<in> Ord \<and> shd js4 \<noteq> shd js2 \<and>
       shd (decr (shd js2) js2) = shd js4 \<and> stl ((decr (shd js2) js2)) = decr (shd js4) js4"
        using stl_decr_shd[of js2] a ae using 1 alw_shift by blast
      show "?\<phi> ls" using 1 js js2 by metis
    qed (metis (no_types, lifting) alw_shift stl_decr_shd)
  }
  thus ?thesis using assms by blast
qed

lemma alw_snth:
  assumes "alw (\<lambda>xs. P (shd (stl xs)) (shd xs)) xs"
  shows "P (xs!!(Suc n)) (xs!! n)"
  using assms
  by (induction n, auto, metis (mono_tags) alw.cases alw_iff_sdrop sdrop_simps(1) sdrop_stl)

lemma F: False
proof-
  define ls where "ls = decr (shd ks) ks"
  have 0: "alw (\<lambda>js. (shd (stl js), shd js) \<in> Ord \<and> shd (stl js) \<noteq> shd js) ls"
    using decr[OF alw_ks alw_ev_ks] unfolding ls_def .
  define Q where "Q = range (snth ls)"  let ?wf = "Wellfounded.wf"
  have Q: "Q \<noteq> {}" unfolding Q_def by auto
  have 1: "?wf (Ord - Id)" using Ord unfolding well_order_on_def by auto
  obtain q where q: "q \<in> Q" and 2: "\<forall>q'. (q',q) \<in> Ord - Id \<longrightarrow> q' \<notin> Q"
    using wfE_min[OF 1] Q by auto
  obtain n where "ls!!n = q" using q unfolding Q_def by auto
  hence "(ls!!(Suc n),q) \<in> Ord - Id" using alw_snth[OF 0] by auto
  thus False using 2 Q_def by blast
qed

end (* context *)

(* Main theorem: *)
theorem infinite_soundness:
  assumes "wf t" and "good t" and "S \<in> structure"
  shows "sat S (fst (root t))"
  using F[OF assms] by auto

end (* context Infinite_Soundness *)


section \<open>Soundness of Cyclic Proof Trees\<close>

(* Cyclic trees *)

datatype (discs_sels) ('sequent, 'rule, 'link) ctree =
  Link 'link |
  cNode  "('sequent,'rule) step" "('sequent, 'rule, 'link) ctree fset"

corecursive treeOf where
  "treeOf pointsTo ct =
   (if \<exists>l l'. pointsTo l = Link l'
    \<comment> \<open>makes sense only if backward links point to normal nodes, not to backwards links:\<close>
     then undefined
     else (case ct of
             Link l \<Rightarrow> treeOf pointsTo (pointsTo l)
            |cNode step cts \<Rightarrow> Node step (fimage (treeOf pointsTo) cts)
          )
   )"
  by (relation "measure (\<lambda>(p,t). case t of Link l' => Suc 0 | _ => 0)") (auto split: ctree.splits)

declare treeOf.code[simp]

context Infinite_Soundness
begin

context
  fixes pointsTo :: "'link \<Rightarrow> ('sequent, 'rule, 'link)ctree"
  assumes pointsTo: "\<forall>l l'. pointsTo l \<noteq> Link l'"
begin

function seqOf where
  "seqOf (Link l) = seqOf (pointsTo l)"
|
  "seqOf (cNode (s,r) _) = s"
  by pat_completeness auto
termination
  by (relation "measure (\<lambda>t. case t of Link l' => Suc 0 | _ => 0)")
    (auto split: ctree.splits simp: pointsTo)

    (* Note: Here, "inductive" instead of "coinductive" would not do! *)
coinductive cwf where
  Node[intro!]: "cwf (pointsTo l) \<Longrightarrow> cwf (Link l)"
|
  cNode[intro]:
  "\<lbrakk>r \<in> R; eff r s (fimage seqOf cts); \<And>ct'. ct' |\<in>| cts \<Longrightarrow> cwf ct'\<rbrakk>
\<Longrightarrow>
cwf (cNode (s,r) cts)"

definition "cgood ct \<equiv> good (treeOf pointsTo ct)"

lemma cwf_Link: "cwf (Link l) \<longleftrightarrow> cwf (pointsTo l)"
  by (auto elim: cwf.cases)

lemma cwf_cNode_seqOf:
  "cwf (cNode (s, r) cts) \<Longrightarrow> eff r s (fimage seqOf cts)"
  by (auto elim: cwf.cases)

lemma treeOf_seqOf[simp]:
  "fst \<circ> root \<circ> treeOf pointsTo = seqOf"
proof(rule ext, unfold o_def)
  fix ct show "fst (root (treeOf pointsTo ct)) = seqOf ct"
    by induct (auto split: ctree.splits simp: pointsTo)
qed

lemma wf_treeOf:
  assumes "cwf ct"
  shows "wf (treeOf pointsTo ct)"
proof-
  {fix t let ?\<phi> = "\<lambda>ct t. cwf ct \<and> t = treeOf pointsTo ct"
    assume "\<exists>ct. ?\<phi> ct t" hence "wf t"
    proof(elim wf.coinduct, safe)
      fix ct let ?t = "treeOf pointsTo ct"
      assume ct: "cwf ct"
      show "
       \<exists>t. treeOf pointsTo ct = t \<and>
           snd (root t) \<in> R \<and>
           effStep (root t) (fimage (fst \<circ> root) (cont t)) \<and>
           (\<forall>t'. t' |\<in>| cont t \<longrightarrow> (\<exists>ct'. ?\<phi> ct' t') \<or> wf t')"
      proof(rule exI[of _ ?t], safe)
        show "snd (root ?t) \<in> R" using pointsTo ct
          by (auto elim: cwf.cases split: ctree.splits simp: cwf_Link)
        show "effStep (root ?t) (fimage (fst \<circ> root) (cont ?t))"
          using pointsTo ct by (auto  elim: cwf.cases split: ctree.splits simp: cwf_Link)
        {fix t' assume t': "t' |\<in>| cont ?t"
          show "\<exists>ct'. ?\<phi> ct' t'"
          proof(cases ct)
            case (Link l)
            then obtain s r cts where pl: "pointsTo l = cNode (s,r) cts"
              using pointsTo by (cases "pointsTo l") auto
            obtain ct' where ct': "ct' |\<in>| cts" and "t' = treeOf pointsTo ct'"
              using t' by (auto simp: Link pl pointsTo split: ctree.splits)
            moreover have "cwf ct'" using ct' ct pl unfolding Link
              by (auto simp: cwf_Link elim: cwf.cases)
            ultimately show ?thesis by blast
          next
            case (cNode step cts)
            then obtain s r where cNode: "ct = cNode (s,r) cts" by (cases step) auto
            obtain ct' where ct': "ct' |\<in>| cts" and "t' = treeOf pointsTo ct'"
              using t' by (auto simp: cNode pointsTo split: ctree.splits)
            moreover have "cwf ct'" using ct' ct unfolding cNode
              by (auto simp: cwf_Link elim: cwf.cases)
            ultimately show ?thesis by blast
          qed
        }
      qed
    qed
  }
  thus ?thesis using assms by blast
qed

theorem cyclic_soundness:
  assumes "cwf ct" and "cgood ct" and "S \<in> structure"
  shows "sat S (seqOf ct)"
  using infinite_soundness wf_treeOf assms
  unfolding cgood_def treeOf_seqOf[symmetric] comp_def
  by blast

end (* context *)

end (* context Infinite_Soundness *)


section \<open>Appendix: The definition of treeOf under more flexible assumptions about pointsTo\<close>

definition rels where
  "rels pointsTo \<equiv> {((pointsTo, pointsTo l'), (pointsTo, Link l')) | l'. True}"

definition rel :: "(('link \<Rightarrow> ('sequent, 'rule, 'link) ctree) \<times> ('sequent, 'rule, 'link) ctree) rel" where
  "rel \<equiv> \<Union> (rels ` {pointsTo. wf {(l, l'). pointsTo l' = Link l}})"

lemma wf_rels[simp]:
  assumes "wf {(l,l'). (pointsTo :: 'link \<Rightarrow> ('sequent, 'rule, 'link)ctree) l' = Link l}"
    (is "wf ?w")
  shows "wf (rels pointsTo)" using wf_map_prod_image
proof -
  define r1 :: "(('link \<Rightarrow> ('sequent, 'rule, 'link) ctree) \<times> ('sequent, 'rule, 'link) ctree) rel" where
    "r1 = {((pointsTo,pointsTo l'), (pointsTo, Link l'::('sequent, 'rule, 'link) ctree)) | l'.
                 (\<forall>l''. pointsTo l' \<noteq> Link l'')}"
  define r2 :: "(('link \<Rightarrow> ('sequent, 'rule, 'link) ctree) \<times> ('sequent, 'rule, 'link) ctree) rel" where
    "r2 = image (map_prod (map_prod id Link) (map_prod id Link)) (inv_image ?w snd)"
  have 0: "rels pointsTo \<subseteq> r1 \<union> r2"
    unfolding rels_def r1_def r2_def unfolding inv_image_def image_Collect by auto
  let ?m = "measure (\<lambda>(tOfL,t). case t of Link l' => Suc 0 | _ => 0)"
  have 1: "wf r1" unfolding r1_def by (rule wf_subset[of ?m]) (auto split: ctree.splits)
  have 2: "wf r2" using assms unfolding r2_def
    by (intro wf_map_prod_image wf_inv_image) (auto simp: inj_on_def)
  have 3: "Domain r1 \<inter> Range r2 = {}" unfolding r1_def r2_def by auto
  show ?thesis using 1 2 3 by (intro wf_subset[OF _ 0] wf_Un) auto
qed

lemma rel: "wf rel"
  unfolding rel_def
  apply(rule wf_UN)
  subgoal by (auto intro: wf_UN)
  unfolding rels_def by auto

corecursive treeOf' where
  "treeOf' pointsTo ct =
   (if \<not> wf {(l',l).  pointsTo l = Link l'}
    \<comment> \<open>makes sense only if backward links point to normal nodes, not to backwards links:\<close>
     then undefined
     else (case ct of
             Link l \<Rightarrow> treeOf' pointsTo (pointsTo l)
            |cNode step cts \<Rightarrow> Node step (fimage (treeOf' pointsTo) cts)
          )
   )"
  apply(relation rel) using rel unfolding rel_def rels_def[abs_def] by auto

(*<*)
end
(*>*)
