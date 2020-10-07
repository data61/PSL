chapter \<open>Addition, Sequences and their Concatenation\<close>

theory OrdArith imports Rank
begin

section \<open>Generalised Addition --- Also for Ordinals\<close>
text \<open>Source: Laurence Kirby, Addition and multiplication of sets
      Math. Log. Quart. 53, No. 1, 52-65 (2007) / DOI 10.1002/malq.200610026
      @{url "http://faculty.baruch.cuny.edu/lkirby/mlqarticlejan2007.pdf"}\<close>

definition
  hadd      :: "hf \<Rightarrow> hf \<Rightarrow> hf"           (infixl "@+" 65)  where
    "hadd x \<equiv> hmemrec (\<lambda>f z. x \<squnion> RepFun z f)"

lemma hadd: "x @+ y = x \<squnion> RepFun y (\<lambda>z. x @+ z)"
  by (metis def_hmemrec RepFun_ecut hadd_def order_refl)

lemma hmem_hadd_E:
  assumes l: "l \<^bold>\<in> x @+ y"
  obtains "l \<^bold>\<in> x" | z where "z \<^bold>\<in> y" "l = x @+ z"
  using l
  by (auto simp: hadd [of x y])

lemma hadd_0_right [simp]: "x @+ 0 = x"
  by (subst hadd) simp

lemma hadd_hinsert_right: "x @+ hinsert y z = hinsert (x @+ y) (x @+ z)"
  by (metis hadd hunion_hinsert_right RepFun_hinsert)

lemma hadd_succ_right [simp]: "x @+ succ y = succ (x @+ y)"
  by (metis hadd_hinsert_right succ_def)

lemma not_add_less_right: "\<not> (x @+ y < x)"
  apply (induct y, auto)
  apply (metis less_supI1 hadd order_less_le)
  done

lemma not_add_mem_right: "\<not> (x @+ y \<^bold>\<in> x)"
  by (metis hadd hmem_not_refl hunion_iff)

lemma hadd_0_left [simp]: "0 @+ x = x"
  by (induct x) (auto simp: hadd_hinsert_right)

lemma hadd_succ_left [simp]: "Ord y \<Longrightarrow> succ x @+ y = succ (x @+ y)"
  by (induct y rule: Ord_induct2) auto

lemma hadd_assoc: "(x @+ y) @+ z = x @+ (y @+ z)"
  by (induct z) (auto simp: hadd_hinsert_right)

lemma RepFun_hadd_disjoint: "x \<sqinter> RepFun y ((@+) x) = 0"
  by (metis hf_equalityI RepFun_iff hinter_iff not_add_mem_right hmem_hempty)


subsection \<open>Cancellation laws for addition\<close>

lemma Rep_le_Cancel: "x \<squnion> RepFun y ((@+) x) \<le> x \<squnion> RepFun z ((@+) x)
                      \<Longrightarrow> RepFun y ((@+) x) \<le> RepFun z ((@+) x)"
  by (auto simp add: not_add_mem_right)

lemma hadd_cancel_right [simp]: "x @+ y = x @+ z \<longleftrightarrow> y=z"
proof (induct y arbitrary: z rule: hmem_induct)
  case (step y z) show ?case
  proof auto
    assume eq: "x @+ y = x @+ z"
    hence  "RepFun y ((@+) x) = RepFun z ((@+) x)"
      by (metis hadd Rep_le_Cancel order_antisym order_refl)
    thus  "y = z"
      by (metis hf_equalityI RepFun_iff step)
  qed
qed

lemma RepFun_hadd_cancel: "RepFun y (\<lambda>z. x @+ z) = RepFun z (\<lambda>z. x @+ z) \<longleftrightarrow> y=z"
  by (metis hadd hadd_cancel_right)

lemma hadd_hmem_cancel [simp]: "x @+ y \<^bold>\<in> x @+ z \<longleftrightarrow> y \<^bold>\<in> z"
  apply (auto simp: hadd [of _ y] hadd [of _ z] not_add_mem_right)
  apply (metis hmem_not_refl hunion_iff)
  apply (metis hadd hadd_cancel_right)
  done

lemma ord_of_add: "ord_of (i+j) = ord_of i @+ ord_of j"
  by (induct j) auto

lemma Ord_hadd: "Ord x \<Longrightarrow> Ord y \<Longrightarrow> Ord (x @+ y)"
  by (induct x rule: Ord_induct2) auto

lemma hmem_self_hadd [simp]: "k1 \<^bold>\<in> k1 @+ k2 \<longleftrightarrow> 0 \<^bold>\<in> k2"
  by (metis hadd_0_right hadd_hmem_cancel)

lemma hadd_commute: "Ord x \<Longrightarrow> Ord y \<Longrightarrow> x @+ y = y @+ x"
  by (induct x rule: Ord_induct2) auto

lemma hadd_cancel_left [simp]: "Ord x \<Longrightarrow> y @+ x = z @+ x \<longleftrightarrow> y=z"
  by (induct x rule: Ord_induct2) auto


subsection \<open>The predecessor function\<close>

definition pred :: "hf \<Rightarrow> hf"
  where "pred x \<equiv> (THE y. succ y = x \<or> x=0 \<and> y=0)"

lemma pred_succ [simp]: "pred (succ x) = x"
  by (simp add: pred_def)

lemma pred_0 [simp]: "pred 0 = 0"
  by (simp add: pred_def)

lemma succ_pred [simp]: "Ord x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> succ (pred x) = x"
  by (metis Ord_cases pred_succ)

lemma pred_mem [simp]: "Ord x \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> pred x \<^bold>\<in> x"
  by (metis succ_iff succ_pred)

lemma Ord_pred [simp]: "Ord x \<Longrightarrow> Ord (pred x)"
  by (metis Ord_in_Ord pred_0 pred_mem)

lemma hadd_pred_right: "Ord y \<Longrightarrow> y \<noteq> 0 \<Longrightarrow> x @+ pred y = pred (x @+ y)"
  by (metis hadd_succ_right pred_succ succ_pred)

lemma Ord_pred_HUnion: "Ord(k) \<Longrightarrow> pred k = \<Squnion>k"
  by (metis HUnion_hempty Ordinal.Ord_pred pred_0 pred_succ)


section \<open>A Concatentation Operation for Sequences\<close>

definition shift :: "hf \<Rightarrow> hf \<Rightarrow> hf"
  where "shift f delta = \<lbrace>v . u \<^bold>\<in> f, \<exists>n y. u = \<langle>n, y\<rangle> \<and> v = \<langle>delta @+ n, y\<rangle>\<rbrace>"

lemma shiftD: "x \<^bold>\<in> shift f delta \<Longrightarrow> \<exists>u. u \<^bold>\<in> f \<and> x = \<langle>delta @+ hfst u, hsnd u\<rangle>"
  by (auto simp: shift_def hsplit_def)

lemma hmem_shift_iff: "\<langle>m, y\<rangle> \<^bold>\<in> shift f delta \<longleftrightarrow> (\<exists>n. m = delta @+ n \<and> \<langle>n, y\<rangle> \<^bold>\<in> f)"
  by (auto simp: shift_def hrelation_def is_hpair_def)

lemma hmem_shift_add_iff [simp]: "\<langle>delta @+ n, y\<rangle> \<^bold>\<in> shift f delta \<longleftrightarrow> \<langle>n, y\<rangle> \<^bold>\<in> f"
  by (metis hadd_cancel_right hmem_shift_iff)

lemma hrelation_shift [simp]: "hrelation (shift f delta)"
  by (auto simp: shift_def hrelation_def hsplit_def)

lemma app_shift [simp]: "app (shift f k) (k @+ j) = app f j"
  by (simp add: app_def)

lemma hfunction_shift_iff [simp]: "hfunction (shift f delta) = hfunction f"
  by (auto simp: hfunction_def hmem_shift_iff)

lemma hdomain_shift_add: "hdomain (shift f delta) = \<lbrace>delta @+ n . n \<^bold>\<in> hdomain f\<rbrace>"
  by  (rule hf_equalityI) (force simp add: hdomain_def hmem_shift_iff)

lemma hdomain_shift_disjoint: "delta \<sqinter> hdomain (shift f delta) = 0"
  by (auto simp: hdomain_def intro!: hf_equalityI)
     (metis shiftD hpair_inject not_add_mem_right)

definition seq_append :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf"
  where "seq_append k f g \<equiv> hrestrict f k \<squnion> shift g k"

lemma hrelation_seq_append [simp]: "hrelation (seq_append k f g)"
  by (simp add: seq_append_def)

lemma Seq_append: "Seq s1 k1 \<Longrightarrow> Seq s2 k2 \<Longrightarrow> Seq (seq_append k1 s1 s2) (k1 @+ k2)"
  apply (auto simp: Seq_def seq_append_def)
  apply (metis hdomain_restr hdomain_shift_disjoint hfunction_hunion hfunction_restr hfunction_shift_iff inf_absorb2 seq_append_def)
  apply (simp add: hdomain_shift_add)
  apply (metis hmem_hadd_E rev_hsubsetD)
  apply (erule hmem_hadd_E, assumption, auto)
  apply (metis Seq_def Seq_iff_app hdomainI hmem_shift_add_iff)
  done

lemma app_hunion1: "x \<^bold>\<notin> hdomain g \<Longrightarrow> app (f \<squnion> g) x = app f x"
  by (auto simp: app_def) (metis hdomainI)

lemma app_hunion2: "x \<^bold>\<notin> hdomain f \<Longrightarrow> app (f \<squnion> g) x = app g x"
  by (auto simp: app_def) (metis hdomainI)

lemma Seq_append_app1: "Seq s k \<Longrightarrow> l \<^bold>\<in> k \<Longrightarrow> app (seq_append k s s') l = app s l"
  apply (auto simp: Seq_def seq_append_def)
  apply (metis app_hunion1 hdomain_shift_disjoint hemptyE hinter_iff app_hrestrict)
  done

lemma Seq_append_app2: "Seq s1 k1 \<Longrightarrow> Seq s2 k2 \<Longrightarrow> l = k1 @+ j \<Longrightarrow> app (seq_append k1 s1 s2) l = app s2 j"
  by (metis seq_append_def app_hunion2 app_shift hdomain_restr hinter_iff not_add_mem_right)


section \<open>Nonempty sequences indexed by ordinals\<close>

definition OrdDom where
 "OrdDom r \<equiv> \<forall>x y. \<langle>x,y\<rangle> \<^bold>\<in> r \<longrightarrow> Ord x"

lemma OrdDom_insf: "\<lbrakk>OrdDom s; Ord k\<rbrakk> \<Longrightarrow> OrdDom (insf s (succ k) y)"
  by (auto simp: insf_def OrdDom_def)

lemma OrdDom_hunion [simp]: "OrdDom (s1 \<squnion> s2) \<longleftrightarrow> OrdDom s1 \<and> OrdDom s2"
  by (auto simp: OrdDom_def)

lemma OrdDom_hrestrict: "OrdDom s \<Longrightarrow> OrdDom (hrestrict s A)"
  by (auto simp: OrdDom_def)

lemma OrdDom_shift: "\<lbrakk>OrdDom s; Ord k\<rbrakk> \<Longrightarrow> OrdDom (shift s k)"
  by (auto simp: OrdDom_def shift_def Ord_hadd)


text \<open>A sequence of positive length ending with @{term y}\<close>
definition LstSeq :: "hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "LstSeq s k y \<equiv> Seq s (succ k) \<and> Ord k \<and> \<langle>k,y\<rangle> \<^bold>\<in> s \<and> OrdDom s"

lemma LstSeq_imp_Seq_succ: "LstSeq s k y \<Longrightarrow> Seq s (succ k)"
  by (metis LstSeq_def)

lemma LstSeq_imp_Seq_same: "LstSeq s k y \<Longrightarrow> Seq s k"
  by (metis LstSeq_imp_Seq_succ Seq_succ_D)

lemma LstSeq_imp_Ord: "LstSeq s k y \<Longrightarrow> Ord k"
  by (metis LstSeq_def)

lemma LstSeq_trunc: "LstSeq s k y \<Longrightarrow> l \<^bold>\<in> k \<Longrightarrow> LstSeq s l (app s l)"
  apply (auto simp: LstSeq_def Seq_iff_app)
  apply (metis Ord_succ Seq_Ord_D mem_succ_iff)
  apply (metis Ord_in_Ord)
  done

lemma LstSeq_insf: "LstSeq s k z \<Longrightarrow> LstSeq (insf s (succ k) y) (succ k) y"
  by (metis OrdDom_insf LstSeq_def Ord_succ_iff Seq_imp_eq_app Seq_insf Seq_succ_iff app_insf_Seq)

lemma app_insf_LstSeq: "LstSeq s k z \<Longrightarrow> app (insf s (succ k) y) (succ k) = y"
  by (metis LstSeq_imp_Seq_succ app_insf_Seq)

lemma app_insf2_LstSeq: "LstSeq s k z \<Longrightarrow> k' \<noteq> succ k \<Longrightarrow> app (insf s (succ k) y) k' = app s k'"
  by (metis LstSeq_imp_Seq_succ app_insf2_Seq)

lemma app_insf_LstSeq_if: "LstSeq s k z \<Longrightarrow> app (insf s (succ k) y) k' = (if k' = succ k then y else app s k')"
  by (metis app_insf2_LstSeq app_insf_LstSeq)

lemma LstSeq_append_app1:
  "LstSeq s k y \<Longrightarrow> l \<^bold>\<in> succ k \<Longrightarrow> app (seq_append (succ k) s s') l = app s l"
  by (metis LstSeq_imp_Seq_succ Seq_append_app1)

lemma LstSeq_append_app2:
  "\<lbrakk>LstSeq s1 k1 y1; LstSeq s2 k2 y2; l = succ k1 @+ j\<rbrakk>
   \<Longrightarrow> app (seq_append (succ k1) s1 s2) l = app s2 j"
   by (metis LstSeq_imp_Seq_succ Seq_append_app2)

lemma Seq_append_pair:
  "\<lbrakk>Seq s1 k1; Seq s2 (succ n);  \<langle>n, y\<rangle> \<^bold>\<in> s2; Ord n\<rbrakk> \<Longrightarrow> \<langle>k1 @+ n, y\<rangle> \<^bold>\<in> (seq_append k1 s1 s2)"
  by (metis hmem_shift_add_iff hunion_iff seq_append_def)

lemma Seq_append_OrdDom: "\<lbrakk>Ord k; OrdDom s1; OrdDom s2\<rbrakk> \<Longrightarrow> OrdDom (seq_append k s1 s2)"
  by (auto simp: seq_append_def OrdDom_hrestrict OrdDom_shift)

lemma LstSeq_append:
  "\<lbrakk>LstSeq s1 k1 y1; LstSeq s2 k2 y2\<rbrakk> \<Longrightarrow> LstSeq (seq_append (succ k1) s1 s2) (succ (k1 @+ k2)) y2"
  apply (auto simp: LstSeq_def Seq_append Ord_hadd Seq_append_pair)
  apply (metis Seq_append hadd_succ_left hadd_succ_right)
  apply (metis Seq_append_pair hadd_succ_left)
  apply (metis Ord_succ Seq_append_OrdDom)
  done

lemma LstSeq_app [simp]: "LstSeq s k y \<Longrightarrow> app s k = y"
  by (metis LstSeq_def Seq_imp_eq_app)


subsection \<open>Sequence-building operators\<close>

definition Builds :: "(hf \<Rightarrow> bool) \<Rightarrow> (hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool) \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "Builds B C s l \<equiv> B (app s l) \<or> (\<exists>m \<^bold>\<in> l. \<exists>n \<^bold>\<in> l. C (app s l) (app s m) (app s n))"

definition BuildSeq :: "(hf \<Rightarrow> bool) \<Rightarrow> (hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool) \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> hf \<Rightarrow> bool"
  where "BuildSeq B C s k y \<equiv> LstSeq s k y \<and> (\<forall>l \<^bold>\<in> succ k. Builds B C s l)"

lemma BuildSeqI: "LstSeq s k y \<Longrightarrow> (\<And>l. l \<^bold>\<in> succ k \<Longrightarrow> Builds B C s l) \<Longrightarrow> BuildSeq B C s k y"
  by (simp add: BuildSeq_def)

lemma BuildSeq_imp_LstSeq: "BuildSeq B C s k y \<Longrightarrow> LstSeq s k y"
  by (metis BuildSeq_def)

lemma BuildSeq_imp_Seq: "BuildSeq B C s k y \<Longrightarrow> Seq s (succ k)"
  by (metis LstSeq_imp_Seq_succ BuildSeq_imp_LstSeq)

lemma BuildSeq_conj_distrib:
 "BuildSeq (\<lambda>x. B x \<and> P x) (\<lambda>x y z. C x y z \<and> P x) s k y \<longleftrightarrow>
  BuildSeq B C s k y \<and> (\<forall>l \<^bold>\<in> succ k. P (app s l))"
  by (auto simp: BuildSeq_def Builds_def)

lemma BuildSeq_mono:
  assumes y: "BuildSeq B C s k y"
      and B: "\<And>x. B x \<Longrightarrow> B' x" and C: "\<And>x y z. C x y z \<Longrightarrow> C' x y z"
  shows "BuildSeq B' C' s k y"
using y
  by (auto simp: BuildSeq_def Builds_def intro!: B C)

lemma BuildSeq_trunc:
  assumes b: "BuildSeq B C s k y"
      and l: "l \<^bold>\<in> k"
  shows "BuildSeq B C s l (app s l)"
proof -
  { fix j
    assume j: "j \<^bold>\<in> succ l"
    have k: "Ord k"
      by (metis BuildSeq_imp_LstSeq LstSeq_def b)
    hence "Builds B C s j"
      by (metis BuildSeq_def OrdmemD b hballE hsubsetD j l succ_iff)
 }
 thus ?thesis using b l
  by (auto simp: BuildSeq_def LstSeq_trunc)
qed


subsection \<open>Showing that Sequences can be Constructed\<close>

lemma Builds_insf: "Builds B C s l \<Longrightarrow> LstSeq s k z \<Longrightarrow> l \<^bold>\<in> succ k \<Longrightarrow> Builds B C (insf s (succ k) y) l"
by (auto simp: HBall_def hmem_not_refl Builds_def app_insf_LstSeq_if simp del: succ_iff)
   (metis hmem_not_sym)

lemma BuildSeq_insf:
  assumes b: "BuildSeq B C s k z"
      and m: "m \<^bold>\<in> succ k"
      and n: "n \<^bold>\<in> succ k"
      and y: "B y \<or> C y (app s m) (app s n)"
shows "BuildSeq B C (insf s (succ k) y) (succ k) y"
proof (rule BuildSeqI)
  show "LstSeq (insf s (succ k) y) (succ k) y"
  by (metis BuildSeq_imp_LstSeq LstSeq_insf b)
next
  fix l
  assume l: "l \<^bold>\<in> succ (succ k)"
  thus "Builds B C (insf s (succ k) y) l"
  proof
    assume l: "l = succ k"
    have "B (app (insf s l y) l) \<or> C (app (insf s l y) l) (app (insf s l y) m) (app (insf s l y) n)"
      by (metis BuildSeq_imp_Seq app_insf_Seq_if b hmem_not_refl l m n y)
    thus "Builds B C (insf s (succ k) y) l" using m n
      by (auto simp: Builds_def l)
  next
    assume l: "l \<^bold>\<in> succ k"
    have  "LstSeq s k z"
      by (metis BuildSeq_imp_LstSeq b)
    thus "Builds B C (insf s (succ k) y) l" using b l
      by (metis hballE Builds_insf BuildSeq_def)
  qed
qed

lemma BuildSeq_insf1:
  assumes b: "BuildSeq B C s k z"
      and y: "B y"
  shows "BuildSeq B C (insf s (succ k) y) (succ k) y"
by (metis BuildSeq_insf b succ_iff y)

lemma BuildSeq_insf2:
  assumes b: "BuildSeq B C s k z"
      and m: "m \<^bold>\<in> k"
      and n: "n \<^bold>\<in> k"
      and y: "C y (app s m) (app s n)"
  shows "BuildSeq B C (insf s (succ k) y) (succ k) y"
  by (metis BuildSeq_insf b m n succ_iff y)

lemma BuildSeq_append:
  assumes s1: "BuildSeq B C s1 k1 y1" and s2: "BuildSeq B C s2 k2 y2"
  shows "BuildSeq B C (seq_append (succ k1) s1 s2) (succ (k1 @+ k2)) y2"
proof (rule BuildSeqI)
  show "LstSeq (seq_append (succ k1) s1 s2) (succ (k1 @+ k2)) y2"
    using assms
    by (metis BuildSeq_imp_LstSeq LstSeq_append)
next
  fix l
  have s1L: "LstSeq s1 k1 y1"
   and s1BC: "\<And>l. l \<^bold>\<in> succ k1 \<Longrightarrow> Builds B C s1 l"
   and s2L: "LstSeq s2 k2 y2"
   and s2BC: "\<And>l. l \<^bold>\<in> succ k2 \<Longrightarrow> Builds B C s2 l"
    using s1 s2 by (auto simp: BuildSeq_def)
  assume l: "l \<^bold>\<in> succ (succ (k1 @+ k2))"
  hence  "l \<^bold>\<in> succ k1 @+ succ k2"
    by (metis LstSeq_imp_Ord hadd_succ_left hadd_succ_right s2L)
  thus "Builds B C (seq_append (succ k1) s1 s2) l"
  proof (rule hmem_hadd_E)
    assume l1: "l \<^bold>\<in> succ k1"
    hence "B (app s1 l) \<or> (\<exists>m\<^bold>\<in>l. \<exists>n\<^bold>\<in>l. C (app s1 l) (app s1 m) (app s1 n))" using s1BC
      by (simp add: Builds_def)
    thus ?thesis
    proof
      assume "B (app s1 l)"
      thus ?thesis
        by (metis Builds_def LstSeq_append_app1 l1 s1L)
    next
      assume "\<exists>m\<^bold>\<in>l. \<exists>n\<^bold>\<in>l. C (app s1 l) (app s1 m) (app s1 n)"
      then obtain m n where mn: "m \<^bold>\<in> l" "n \<^bold>\<in> l" and C: "C (app s1 l) (app s1 m) (app s1 n)"
        by blast
      also have "m \<^bold>\<in> succ k1" "n \<^bold>\<in> succ k1"
        by (metis LstSeq_def Ord_trans l1 mn s1L succ_iff)+
      ultimately have "C (app (seq_append (succ k1) s1 s2) l)
                         (app (seq_append (succ k1) s1 s2) m)
                         (app (seq_append (succ k1) s1 s2) n)"
        using s1L l1
        by (simp add: LstSeq_append_app1)
      thus "Builds B C (seq_append (succ k1) s1 s2) l" using mn
        by (auto simp: Builds_def)
    qed
  next
    fix z
    assume z: "z \<^bold>\<in> succ k2" and l2: "l = succ k1 @+ z"
    hence "B (app s2 z) \<or> (\<exists>m\<^bold>\<in>z. \<exists>n\<^bold>\<in>z. C (app s2 z) (app s2 m) (app s2 n))" using s2BC
      by (simp add: Builds_def)
    thus ?thesis
    proof
      assume "B (app s2 z)"
      thus ?thesis
        by (metis Builds_def LstSeq_append_app2 l2 s1L s2L)
    next
      assume "\<exists>m\<^bold>\<in>z. \<exists>n\<^bold>\<in>z. C (app s2 z) (app s2 m) (app s2 n)"
      then obtain m n where mn: "m \<^bold>\<in> z" "n \<^bold>\<in> z" and C: "C (app s2 z) (app s2 m) (app s2 n)"
        by blast
      also have "m \<^bold>\<in> succ k2" "n \<^bold>\<in> succ k2" using mn
        by (metis LstSeq_def Ord_trans z s2L succ_iff)+
      ultimately have "C (app (seq_append (succ k1) s1 s2) l)
                         (app (seq_append (succ k1) s1 s2) (succ k1 @+ m))
                         (app (seq_append (succ k1) s1 s2) (succ k1 @+ n))"
        using s1L s2L l2 z
        by (simp add: LstSeq_append_app2)
      thus "Builds B C (seq_append (succ k1) s1 s2) l" using mn l2
        by (auto simp: Builds_def HBall_def)
    qed
  qed
qed

lemma BuildSeq_combine:
  assumes b1: "BuildSeq B C s1 k1 y1" and b2: "BuildSeq B C s2 k2 y2"
      and y: "C y y1 y2"
  shows "BuildSeq B C (insf (seq_append (succ k1) s1 s2) (succ (succ (k1 @+ k2))) y) (succ (succ (k1 @+ k2))) y"
proof -
  have k2: "Ord k2"  using b2
    by (auto simp: BuildSeq_def LstSeq_def)
  show ?thesis
  proof (rule BuildSeq_insf [where m=k1 and n="succ(k1@+k2)"])
    show "BuildSeq B C (seq_append (succ k1) s1 s2) (succ (k1 @+ k2)) y2"
      by (rule BuildSeq_append [OF b1 b2])
  next
    show "k1 \<^bold>\<in> succ (succ (k1 @+ k2))" using k2
      by (metis hadd_0_right hmem_0_Ord hmem_self_hadd succ_iff)
  next
    show "succ (k1 @+ k2) \<^bold>\<in> succ (succ (k1 @+ k2))"
      by (metis succ_iff)
  next
    have [simp]: "app (seq_append (succ k1) s1 s2) k1 = y1"
      by (metis b1 BuildSeq_imp_LstSeq LstSeq_app LstSeq_append_app1 succ_iff)
    have [simp]: "app (seq_append (succ k1) s1 s2) (succ (k1 @+ k2)) = y2"
      by (metis b1 b2 k2 BuildSeq_imp_LstSeq LstSeq_app LstSeq_append_app2 hadd_succ_left)
    show "B y \<or>
          C y (app (seq_append (succ k1) s1 s2) k1)
              (app (seq_append (succ k1) s1 s2) (succ (k1 @+ k2)))"
      using y by simp
  qed
qed

lemma LstSeq_1: "LstSeq \<lbrace>\<langle>0, y\<rangle>\<rbrace> 0 y"
 by (auto simp: LstSeq_def One_hf_eq_succ Seq_ins OrdDom_def)

lemma BuildSeq_1: "B y \<Longrightarrow> BuildSeq B C \<lbrace>\<langle>0, y\<rangle>\<rbrace> 0 y"
  by (auto simp: BuildSeq_def Builds_def LstSeq_1)

lemma BuildSeq_exI: "B t \<Longrightarrow> \<exists>s k. BuildSeq B C s k t"
  by (metis BuildSeq_1)


subsection \<open>Proving Properties of Given Sequences\<close>

lemma BuildSeq_succ_E:
    assumes s: "BuildSeq B C s k y"
      obtains "B y" |  m n where "m \<^bold>\<in> k" "n \<^bold>\<in> k" "C y (app s m) (app s n)"
proof -
  have Bs: "Builds B C s k" and apps: "app s k = y" using s
   by (auto simp: BuildSeq_def)
 hence "B y \<or> (\<exists>m \<^bold>\<in> k. \<exists>n \<^bold>\<in> k. C y (app s m) (app s n))"
   by (metis Builds_def apps Bs)
 thus ?thesis using that
   by auto
qed

lemma BuildSeq_induct [consumes 1, case_names B C]:
  assumes major: "BuildSeq B C s k a"
      and B: "\<And>x. B x \<Longrightarrow> P x"
      and C: "\<And>x y z. C x y z \<Longrightarrow> P y \<Longrightarrow> P z \<Longrightarrow> P x"
  shows "P a"
proof -
  have "Ord k" using assms
    by (auto simp: BuildSeq_def LstSeq_def)
  hence "\<And>a s. BuildSeq B C s k a \<Longrightarrow> P a"
    by (induction k rule: Ord_induct) (metis BuildSeq_trunc BuildSeq_succ_E B C)
  thus ?thesis
    by (metis major)
qed

definition BuildSeq2 :: "[[hf,hf] \<Rightarrow> bool, [hf,hf,hf,hf,hf,hf] \<Rightarrow> bool, hf, hf, hf, hf] \<Rightarrow> bool"
  where "BuildSeq2 B C s k y y' \<equiv>
         BuildSeq (\<lambda>p. \<exists>x x'. p = \<langle>x,x'\<rangle> \<and> B x x')
                  (\<lambda>p q r. \<exists>x x' y y' z z'. p = \<langle>x,x'\<rangle> \<and> q = \<langle>y,y'\<rangle> \<and> r = \<langle>z,z'\<rangle> \<and> C x x' y y' z z')
                  s k \<langle>y,y'\<rangle>"

lemma BuildSeq2_combine:
  assumes b1: "BuildSeq2 B C s1 k1 y1 y1'" and b2: "BuildSeq2 B C s2 k2 y2 y2'"
      and y: "C y y' y1 y1' y2 y2'"
  shows "BuildSeq2 B C (insf (seq_append (succ k1) s1 s2) (succ (succ (k1 @+ k2))) \<langle>y, y'\<rangle>)
                       (succ (succ (k1 @+ k2))) y y'"
  using assms
  apply (unfold BuildSeq2_def)
  apply (blast intro: BuildSeq_combine)
  done

lemma BuildSeq2_1: "B y y' \<Longrightarrow> BuildSeq2 B C \<lbrace>\<langle>0, y, y'\<rangle>\<rbrace> 0 y y'"
  by (auto simp: BuildSeq2_def BuildSeq_1)

lemma BuildSeq2_exI: "B t t' \<Longrightarrow> \<exists>s k. BuildSeq2 B C s k t t'"
  by (metis BuildSeq2_1)

lemma BuildSeq2_induct [consumes 1, case_names B C]:
  assumes "BuildSeq2 B C s k a a'"
      and B: "\<And>x x'. B x x' \<Longrightarrow> P x x'"
      and C: "\<And>x x' y y' z z'. C x x' y y' z z' \<Longrightarrow> P y y' \<Longrightarrow> P z z' \<Longrightarrow> P x x'"
  shows "P a a'"
using assms
apply (simp add: BuildSeq2_def)
apply (drule BuildSeq_induct [where P = "\<lambda>\<langle>x,x'\<rangle>. P x x'"])
apply (auto intro: B C)
done

definition BuildSeq3
   :: "[[hf,hf,hf] \<Rightarrow> bool, [hf,hf,hf,hf,hf,hf,hf,hf,hf] \<Rightarrow> bool, hf, hf, hf, hf, hf] \<Rightarrow> bool"
  where "BuildSeq3 B C s k y y' y'' \<equiv>
         BuildSeq (\<lambda>p. \<exists>x x' x''. p = \<langle>x,x',x''\<rangle> \<and> B x x' x'')
                  (\<lambda>p q r. \<exists>x x' x'' y y' y'' z z' z''.
                           p = \<langle>x,x',x''\<rangle> \<and> q = \<langle>y,y',y''\<rangle> \<and> r = \<langle>z,z',z''\<rangle> \<and>
                           C x x' x'' y y' y'' z z' z'')
                  s k \<langle>y,y',y''\<rangle>"

lemma BuildSeq3_combine:
  assumes b1: "BuildSeq3 B C s1 k1 y1 y1' y1''" and b2: "BuildSeq3 B C s2 k2 y2 y2' y2''"
      and y: "C y y' y'' y1 y1' y1'' y2 y2' y2''"
  shows "BuildSeq3 B C (insf (seq_append (succ k1) s1 s2) (succ (succ (k1 @+ k2))) \<langle>y, y', y''\<rangle>)
                       (succ (succ (k1 @+ k2))) y y' y''"
  using assms
  apply (unfold BuildSeq3_def)
  apply (blast intro: BuildSeq_combine)
  done

lemma BuildSeq3_1: "B y y' y'' \<Longrightarrow> BuildSeq3 B C \<lbrace>\<langle>0, y, y', y''\<rangle>\<rbrace> 0 y y' y''"
  by (auto simp: BuildSeq3_def BuildSeq_1)

lemma BuildSeq3_exI: "B t t' t'' \<Longrightarrow> \<exists>s k. BuildSeq3 B C s k t t' t''"
  by (metis BuildSeq3_1)

lemma BuildSeq3_induct [consumes 1, case_names B C]:
  assumes "BuildSeq3 B C s k a a' a''"
      and B: "\<And>x x' x''. B x x' x'' \<Longrightarrow> P x x' x''"
      and C: "\<And>x x' x'' y y' y'' z z' z''. C x x' x'' y y' y'' z z' z'' \<Longrightarrow> P y y' y'' \<Longrightarrow> P z z' z'' \<Longrightarrow> P x x' x''"
  shows "P a a' a''"
using assms
apply (simp add: BuildSeq3_def)
apply (drule BuildSeq_induct [where P = "\<lambda>\<langle>x,x',x''\<rangle>. P x x' x''"])
apply (auto intro: B C)
done


section \<open>A Unique Predecessor for every non-empty set\<close>

lemma Rep_hf_0 [simp]: "Rep_hf 0 = 0"
  by (metis Abs_hf_inverse HF.HF_def UNIV_I Zero_hf_def image_empty set_encode_empty)

lemma hmem_imp_less: "x \<^bold>\<in> y \<Longrightarrow> Rep_hf x < Rep_hf y"
apply (auto simp: hmem_def hfset_def set_decode_def Abs_hf_inverse)
apply (metis div_less even_zero le_less_trans less_two_power not_less)
done

lemma hsubset_imp_le: "x \<le> y \<Longrightarrow> Rep_hf x \<le> Rep_hf y"
  apply (auto simp: less_eq_hf_def hmem_def hfset_def Abs_hf_inverse)
  apply (cases x rule: Abs_hf_cases)
  apply (cases y rule: Abs_hf_cases, auto)
  apply (rule subset_decode_imp_le)
  apply (auto simp: Abs_hf_inverse [OF UNIV_I])
  apply (metis Abs_hf_inverse UNIV_I imageE imageI)
  done

lemma diff_hmem_imp_less: assumes "x \<^bold>\<in> y" shows "Rep_hf (y - \<lbrace>x\<rbrace>) < Rep_hf y"
proof -
  have  "Rep_hf (y - \<lbrace>x\<rbrace>) \<le> Rep_hf y"
    by (metis hdiff_iff hsubsetI hsubset_imp_le)
  moreover
  have "Rep_hf (y - \<lbrace>x\<rbrace>) \<noteq> Rep_hf y" using assms
    by (metis Rep_hf_inject hdiff_iff hinsert_iff)
  ultimately show ?thesis
    by (metis le_neq_implies_less)
qed

definition least :: "hf \<Rightarrow> hf"
  where "least a \<equiv> (THE x. x \<^bold>\<in> a \<and> (\<forall>y. y \<^bold>\<in> a \<longrightarrow> Rep_hf x \<le> Rep_hf y))"

lemma least_equality:
  assumes "x \<^bold>\<in> a" and "\<And>y. y \<^bold>\<in> a \<Longrightarrow> Rep_hf x \<le> Rep_hf y"
  shows "least a = x"
unfolding least_def
apply (rule the_equality)
apply (metis assms)
apply (metis Rep_hf_inverse assms eq_iff)
done

lemma leastI2_order:
  assumes "x \<^bold>\<in> a"
    and "\<And>y. y \<^bold>\<in> a \<Longrightarrow> Rep_hf x \<le> Rep_hf y"
    and "\<And>z. z \<^bold>\<in> a \<Longrightarrow> \<forall>y. y \<^bold>\<in> a \<longrightarrow> Rep_hf z \<le> Rep_hf y \<Longrightarrow> Q z"
  shows "Q (least a)"
by (metis assms least_equality)

lemma nonempty_imp_ex_least: "a \<noteq> 0 \<Longrightarrow> \<exists>x. x \<^bold>\<in> a \<and> (\<forall>y. y \<^bold>\<in> a \<longrightarrow> Rep_hf x \<le> Rep_hf y)"
proof (induction a rule: hf_induct)
  case 0 thus ?case by simp
next
  case (hinsert u v)
  show ?case
    proof (cases "v=0")
     case True thus ?thesis
       by (rule_tac x=u in exI, simp)
    next
      case False
      thus ?thesis
        by (metis dual_order.trans eq_iff hinsert.IH(2) hmem_hinsert
                  less_eq_insert1_iff linear)
    qed
qed

lemma least_hmem: "a \<noteq> 0 \<Longrightarrow> least a \<^bold>\<in> a"
apply (frule nonempty_imp_ex_least, clarify)
apply (rule leastI2_order, auto)
done

end
