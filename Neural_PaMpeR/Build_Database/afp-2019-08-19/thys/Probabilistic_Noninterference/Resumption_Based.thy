section \<open>Resumption-Based Noninterference\<close>

theory Resumption_Based
imports Language_Semantics
begin

(* We introduce the resumption based notions: strong probabilistic bisimilarity \<approx>s and
01- probabilistic bisimilarity \<approx>01, and prove their basic properties.  E.g., we prove that
\<approx>s is symmetric and transitive.
*)

type_synonym 'a rel = "('a \<times>'a) set"

subsection \<open>Preliminaries\<close>

lemma int_emp[simp]:
assumes "i > 0"
shows "{..<i} \<noteq> {}"
by (metis assms emptyE lessThan_iff)

lemma inj_on_inv_into[simp]:
assumes "inj_on F P"
shows "inv_into P F ` (F ` P) = P"
using assms by auto

lemma inj_on_inv_into2[simp]:
"inj_on (inv_into P F) (F ` P)"
by (metis Hilbert_Choice.inj_on_inv_into subset_refl)

lemma refl_gfp:
assumes 1: "mono Retr" and 2: "\<And> theta. refl theta \<Longrightarrow> refl (Retr theta)"
shows "refl (gfp Retr)"
proof-
  define bis where "bis = gfp Retr"
  define th where "th = Id Un bis"
  have "bis \<subseteq> Retr bis"
  using 1 unfolding bis_def by (metis gfp_unfold subset_refl)
  also have "... \<subseteq> Retr th" using 1 unfolding mono_def th_def by auto
  finally have "bis \<subseteq> Retr th" .
  moreover
  {have "refl th" unfolding th_def by (metis Un_commute refl_reflcl)
   hence "refl (Retr th)" using 2 by simp
  }
  ultimately have "Id \<subseteq> Retr th" unfolding th_def refl_on_def by auto
  hence "Id \<subseteq> bis" using 1 coinduct unfolding th_def bis_def by blast
  thus ?thesis unfolding bis_def refl_on_def by auto
qed

lemma sym_gfp:
assumes 1: "mono Retr" and 2: "\<And> theta. sym theta \<Longrightarrow> sym (Retr theta)"
shows "sym (gfp Retr)"
proof-
  define bis where "bis = gfp Retr"
  define th where "th = bis ^-1 Un bis"
  have "bis \<subseteq> Retr bis"
  using 1 unfolding bis_def by (metis gfp_unfold subset_refl)
  also have "... \<subseteq> Retr th" using 1 unfolding mono_def th_def by auto
  finally have "bis \<subseteq> Retr th" .
  moreover
  {have "sym th" unfolding th_def by (metis Un_commute sym_Un_converse)
   hence "sym (Retr th)" using 2 by simp
  }
  ultimately have "bis ^-1 \<subseteq> Retr th"
  by (metis Un_absorb2 Un_commute Un_upper1 converse_Un sym_conv_converse_eq)
  hence "bis ^-1 \<subseteq> bis" using 1 coinduct[of Retr "bis ^-1"] unfolding th_def bis_def by blast
  thus ?thesis unfolding bis_def sym_def by blast
qed

lemma trancl_trans[simp]:
assumes "trans R"
shows "P ^+ \<subseteq> R \<longleftrightarrow> P \<subseteq> R"
proof-
  {assume "P \<subseteq> R"
   hence "P ^+ \<subseteq> R ^+" using trancl_mono by auto
   also have "R ^+ = R" using assms trans_trancl by auto
   finally have "P ^+ \<subseteq> R" .
  }
  thus ?thesis by auto
qed

lemma trans_gfp:
assumes 1: "mono Retr" and 2: "\<And> theta. trans theta \<Longrightarrow> trans (Retr theta)"
shows "trans (gfp Retr)"
proof-
  define bis where "bis = gfp Retr"
  define th where "th = bis ^+"
  have "bis \<subseteq> Retr bis"
  using 1 unfolding bis_def by (metis gfp_unfold subset_refl)
  also have "... \<subseteq> Retr th" using 1 unfolding mono_def th_def
    by (metis trancl_trans order_refl trans_trancl)
  finally have "bis \<subseteq> Retr th" .
  moreover
  {have "trans th" unfolding th_def by (metis th_def trans_trancl)
   hence "trans (Retr th)" using 2 by simp
  }
  ultimately have "bis ^+ \<subseteq> Retr th" by simp
  hence "bis ^+ \<subseteq> bis" using 1 coinduct unfolding th_def bis_def
  by (metis bis_def gfp_upperbound th_def)
  thus ?thesis unfolding bis_def trans_def by auto
qed

lemma O_subset_trans:
assumes "r O r \<subseteq> r"
shows "trans r"
using assms unfolding trans_def by blast

lemma trancl_imp_trans:
assumes "r ^+ \<subseteq> r"
shows "trans r"
by (metis Int_absorb1 Int_commute trancl_trans assms subset_refl trans_trancl)

lemma sym_trans_gfp:
assumes 1: "mono Retr" and 2: "\<And> theta. sym theta \<and> trans theta \<Longrightarrow> sym (Retr theta) \<and> trans (Retr theta)"
shows "sym (gfp Retr) \<and> trans (gfp Retr)"
proof-
  define bis where "bis = gfp Retr"
  define th where "th = (bis Un bis ^-1) ^+"
  have "bis \<subseteq> Retr bis"
  using 1 unfolding bis_def by (metis gfp_unfold subset_refl)
  also have "... \<subseteq> Retr th" using 1 unfolding mono_def th_def
    by (metis inf_sup_absorb le_iff_inf sup_aci(2) trancl_unfold)
  finally have "bis \<subseteq> Retr th" .
  hence "(bis Un bis ^-1) ^+ \<subseteq> ((Retr th) Un (Retr th) ^-1) ^+" by auto
  moreover
  {have "sym th" unfolding th_def by (metis sym_Un_converse sym_trancl)
   moreover have "trans th" unfolding th_def by (metis th_def trans_trancl)
   ultimately have "sym (Retr th) \<and> trans (Retr th)" using 2 by simp
   hence "((Retr th) Un (Retr th) ^-1) ^+ \<subseteq> Retr th"
   by (metis Un_absorb subset_refl sym_conv_converse_eq trancl_id)
  }
  ultimately have "(bis Un bis ^-1) ^+ \<subseteq> Retr th" by blast
  hence "(bis Un bis ^-1) ^+ \<subseteq> bis" using 1 coinduct unfolding th_def bis_def
  by (metis bis_def gfp_upperbound th_def)
  hence "bis ^-1 \<subseteq> bis" and "bis ^+ \<subseteq> bis"
  apply(metis equalityI gfp_upperbound le_supI1 subset_refl sym_Un_converse sym_conv_converse_eq th_def trancl_id trancl_imp_trans)
  by (metis Un_absorb \<open>(bis \<union> bis\<inverse>)\<^sup>+ \<subseteq> bis\<close> less_supI1 psubset_eq sym_Un_converse sym_conv_converse_eq sym_trancl trancl_id trancl_imp_trans)
  thus ?thesis unfolding bis_def sym_def using trancl_imp_trans by auto
qed

subsection \<open>Infrastructure for partitions\<close>

(* Being a partition *)
definition part where
"part J P \<equiv>
 Union P = J \<and>
 (\<forall> J1 J2. J1 \<in> P \<and> J2 \<in> P \<and> J1 \<noteq> J2 \<longrightarrow> J1 \<inter> J2 = {})"

(* gen P I is the set generated from I using intersections with sets of P  *)
inductive_set gen
for P :: "'a set set" and I :: "'a set" where
 incl[simp]: "i \<in> I \<Longrightarrow> i \<in> gen P I"
|ext[simp]: "\<lbrakk>J \<in> P; j0 \<in> J; j0 \<in> gen P I; j \<in> J\<rbrakk> \<Longrightarrow> j \<in> gen P I"

(* Partition generated by a set *)
definition partGen where
"partGen P \<equiv> {gen P I | I . I \<in> P}"

(* finer P Q means: as a partition, P is finer than Q;
   regarding P and Q as equivalence relations, we have Q included in P *)
definition finer where
"finer P Q \<equiv>
 (\<forall> J \<in> Q. J = Union {I \<in> P . I \<subseteq> J}) \<and>
 (P \<noteq> {} \<longrightarrow> Q \<noteq> {})"

(* The join of two partitions; in terms of equivalence relations,
   this is the smallest equivalence containing both *)
definition partJoin where
"partJoin P Q \<equiv> partGen (P \<union> Q)"

(* Compatibility of a function f w.r.t. a set I versus a relation theta *)
definition compat where
"compat I theta f \<equiv> \<forall> i j. {i, j} \<subseteq> I \<and> i \<noteq> j \<longrightarrow> (f i, f j) \<in> theta"

(* Compatibility of a function f w.r.t. a partition P versus a relation theta;
if P is regarded as an equivalence class, we have the standard notion of compatibility *)
definition partCompat where
"partCompat P theta f \<equiv>
 \<forall> I \<in> P. compat I theta f"

(* Lifting a function F on a partition P to elements II of a potentially coarser partition *)
definition lift where
"lift P F II \<equiv> Union {F I | I . I \<in> P \<and> I \<subseteq> II}"

text\<open>part:\<close>

lemma part_emp[simp]:
"part J (insert {} P) = part J P"
unfolding part_def by auto

lemma finite_part[simp]:
assumes "finite I" and "part I P"
shows "finite P"
using assms finite_UnionD unfolding part_def by auto

lemma part_sum:
  assumes P: "part {..<n::nat} P"
  shows "(\<Sum>i<n. f i) = (\<Sum>p\<in>P. \<Sum>i\<in>p. f i)"
proof (subst sum.Union_disjoint [symmetric, simplified])
  show "\<forall>p\<in>P. finite p"
  proof
    fix p assume "p \<in> P"
    with P have "p \<subseteq> {0..<n}" by (auto simp: part_def)
    then show "finite p" by (rule finite_subset) simp
  qed
  show "\<forall>A\<in>P. \<forall>B\<in>P. A \<noteq> B \<longrightarrow> A \<inter> B = {}"
    using P by (auto simp: part_def)
  show "sum f {..<n} = sum f (\<Union>P)"
    using P by (auto simp: part_def atLeast0LessThan)
qed

lemma part_Un[simp]:
assumes "part I1 P1" and "part I2 P2" and "I1 Int I2 = {}"
shows "part (I1 Un I2) (P1 Un P2)"
  using assms unfolding part_def
  by (metis Union_Un_distrib Union_disjoint inf_aci(1) mem_simps(3))

lemma part_Un_singl[simp]:
assumes "part K P" and "\<And> I. I \<in> P \<Longrightarrow> I0 Int I = {}"
shows "part (I0 Un K) ({I0} Un P)"
using assms unfolding part_def
by (metis complete_lattice_class.Sup_insert Int_commute insert_iff insert_is_Un)

lemma part_Un_singl2:
assumes "K01 = I0 Un K1"
and "part K1 P" and "\<And> I. I \<in> P \<Longrightarrow> I0 Int I = {}"
shows "part K01 ({I0} Un P)"
using assms part_Un_singl by blast

lemma part_UN:
assumes "\<And> n. n \<in> N \<Longrightarrow> part (I n) (P n)"
and "\<And> n1 n2. {n1,n2} \<subseteq> N \<and> n1 \<noteq> n2 \<Longrightarrow> I n1 \<inter> I n2 = {}"
shows "part (UN n : N. I n) (UN n : N. P n)"
using assms unfolding part_def apply auto
apply (metis UnionE)
apply (metis Union_upper disjoint_iff_not_equal insert_absorb insert_subset)
by (metis UnionI disjoint_iff_not_equal)

text\<open>gen:\<close>

lemma incl_gen[simp]:
"I \<subseteq> gen P I"
by auto

lemma gen_incl_Un:
"gen P I \<subseteq> I \<union> (Union P)"
proof
  fix j assume "j \<in> gen P I"
  thus "j \<in> I \<union> \<Union>P" apply induct by blast+
qed

lemma gen_incl:
assumes "I \<in> P"
shows "gen P I \<subseteq> Union P"
using assms gen_incl_Un[of P I] by blast

lemma finite_gen:
assumes "finite P" and "\<And> J. J \<in> P \<Longrightarrow> finite J" and "finite I"
shows "finite (gen P I)"
by (metis assms finite_Union gen_incl_Un infinite_Un infinite_super)

lemma subset_gen[simp]:
assumes "J \<in> P" and "gen P I \<inter> J \<noteq> {}"
shows "J \<subseteq> gen P I"
using assms gen.ext[of J P _ I] by blast

lemma gen_subset_gen[simp]:
assumes "J \<in> P" and "gen P I \<inter> J \<noteq> {}"
shows "gen P J \<subseteq> gen P I"
proof-
  have J: "J \<subseteq> gen P I" using assms by auto
  show ?thesis proof
    fix i assume "i \<in> gen P J"
    thus "i \<in> gen P I"
    proof induct
      case (ext J' j0 j)
      thus ?case
      using gen.ext[of J' P j0 I j] by blast
    qed (insert J, auto)
  qed
qed

lemma gen_mono[simp]:
assumes "I \<subseteq> J"
shows "gen P I \<subseteq> gen P J"
proof
  fix i assume "i \<in> gen P I" thus "i \<in> gen P J"
  proof induct
    case (ext I' j0 j)
    thus ?case
    using gen.ext[of I' P j0 J j] by blast
  qed (insert assms, auto)
qed

lemma gen_idem[simp]:
"gen P (gen P I) = gen P I"
proof-
  define J where "J = gen P I"
  have "I \<subseteq> J" unfolding J_def by auto
  hence "gen P I \<subseteq> gen P J" by simp
  moreover have "gen P J \<subseteq> gen P I"
  proof
    fix i assume "i \<in> gen P J"
    thus "i \<in> gen P I"
    proof induct
      case (ext J' j0 j)
      thus ?case
        using gen.ext[of J' P j0 I j] by blast
    qed (unfold J_def, auto)
  qed
  ultimately show ?thesis unfolding J_def by auto
qed

lemma gen_nchotomy:
assumes "J \<in> P"
shows "J \<subseteq> gen P I \<or> gen P I \<inter> J = {}"
using assms subset_gen[of J P I] by blast

lemma gen_Union:
assumes "I \<in> P"
shows "gen P I = Union {J \<in> P . J \<subseteq> gen P I}"
proof safe
  fix i assume i: "i \<in> gen P I"
  then obtain J where J: "J \<in> P"  "i \<in> J" using assms gen_incl by blast
  hence "J \<subseteq> gen P I" using assms i gen_nchotomy by auto
  thus "i \<in> \<Union>{J \<in> P. J \<subseteq> gen P I}" using J by auto
qed auto

lemma subset_gen2:
assumes *: "{I,J} \<subseteq> P" and **: "gen P I \<inter> gen P J \<noteq> {}"
shows "I \<subseteq> gen P J"
proof-
  {fix i0 i assume i0: "i0 \<in> I \<and> i0 \<notin> gen P J"
   assume "i \<in> gen P I"
   hence "i \<notin> gen P J"
   proof induct
     case (incl i)
     thus ?case using i0 gen_nchotomy[of I P J] * by blast
   next
     case (ext I' j0 j)
     thus ?case
     using gen.ext[of I' P j0 J j] gen_nchotomy[of I' P J] by blast
   qed
  }
  thus ?thesis using assms by auto
qed

lemma gen_subset_gen2[simp]:
assumes "{I,J} \<subseteq> P" and "gen P I \<inter> gen P J \<noteq> {}"
shows "gen P I \<subseteq> gen P J"
proof
  fix i assume "i \<in> gen P I"
  thus "i \<in> gen P J"
  proof induct
    case (incl i)
    thus ?case
    using assms subset_gen2 by auto
  next
    case (ext I' j0 j)
    thus ?case
    using gen.ext[of I' P j0 J j] by blast
  qed
qed

lemma gen_eq_gen:
assumes "{I,J} \<subseteq> P" and "gen P I \<inter> gen P J \<noteq> {}"
shows "gen P I = gen P J"
using assms gen_subset_gen2[of I J P] gen_subset_gen2[of J I P] by blast

lemma gen_empty[simp]:
"gen P {} = {}"
proof-
  {fix j assume "j \<in> gen P {}" hence False
   apply induct by auto
  }
  thus ?thesis by auto
qed

lemma gen_empty2[simp]:
"gen {} I = I"
proof-
  {fix j assume "j \<in> gen {} I" hence "j \<in> I"
   apply induct by auto
  }
  thus ?thesis by auto
qed

lemma emp_gen[simp]:
assumes "gen P I = {}"
shows "I = {}"
by (metis all_not_in_conv assms gen.incl)

text\<open>partGen:\<close>

lemma partGen_ex:
assumes "I \<in> P"
shows "\<exists> J \<in> partGen P. I \<subseteq> J"
using assms unfolding partGen_def
apply(intro bexI[of _ "gen P I"]) by auto

lemma ex_partGen:
assumes "J \<in> partGen P" and j: "j \<in> J"
shows "\<exists> I \<in> P. j \<in> I"
proof-
  obtain I0 where I0: "I0 \<in> P" and J: "J = gen P I0"
  using assms unfolding partGen_def by auto
  thus ?thesis using j gen_incl[of I0 P] by auto
qed

lemma Union_partGen: "\<Union> (partGen P) = \<Union> P"
using ex_partGen[of _ P] partGen_ex[of _ P] by fastforce

lemma Int_partGen:
assumes *: "{I,J} \<subseteq> partGen P" and **: "I \<inter> J \<noteq> {}"
shows "I = J"
proof-
  obtain I0 where I0: "I0 \<in> P" and I: "I = gen P I0"
  using assms unfolding partGen_def by auto
  obtain J0 where J0: "J0 \<in> P" and J: "J = gen P J0"
  using assms unfolding partGen_def by auto
  show ?thesis using gen_eq_gen[of I0 J0 P] I0 J0 ** unfolding I J by blast
qed

lemma part_partGen:
"part (Union P) (partGen P)"
unfolding part_def apply(intro conjI allI impI)
apply (metis Union_partGen)
using Int_partGen by blast

lemma finite_partGen[simp]:
assumes "finite P"
shows "finite (partGen P)"
using assms unfolding partGen_def by auto

lemma emp_partGen[simp]:
assumes "{} \<notin> P"
shows "{} \<notin> partGen P"
using assms unfolding partGen_def using emp_gen[of P] by blast

text\<open>finer:\<close>

lemma finer_partGen:
"finer P (partGen P)"
unfolding finer_def partGen_def using gen_Union by auto

lemma finer_nchotomy:
assumes P: "part I0 P" and Q: "part I0 Q" and PQ: "finer P Q"
and I: "I \<in> P" and II: "II \<in> Q"
shows "I \<subseteq> II \<or> (I \<inter> II = {})"
proof(cases "I \<inter> II = {}")
  case False
  then obtain i where i: "i \<in> I \<and> i \<in> II" by auto
  then obtain I' where "i \<in> I'" and I': "I' \<in> P \<and> I' \<subseteq> II"
  using PQ II unfolding finer_def by blast
  hence "I Int I' \<noteq> {}" using i by blast
  hence "I = I'" using I I' P unfolding part_def by auto
  hence "I \<subseteq> II" using I' by simp
  thus ?thesis by auto
qed auto

lemma finer_ex:
assumes P: "part I0 P" and Q: "part I0 Q" and PQ: "finer P Q"
and I: "I \<in> P"
shows "\<exists> II. II \<in> Q \<and> I \<subseteq> II"
proof(cases "I = {}")
  case True
  have "Q \<noteq> {}" using I PQ unfolding finer_def by auto
  then obtain JJ where "JJ \<in> Q" by auto
  with True show ?thesis by blast
next
  case False
  then obtain i where i: "i \<in> I" by auto
  hence "i \<in> I0" using I P unfolding part_def by auto
  then obtain II where II: "II \<in> Q" and "i \<in> II" using Q unfolding part_def by auto
  hence "I Int II \<noteq> {}" using i by auto
  thus ?thesis using assms I II finer_nchotomy[of I0 P Q I II] by auto
qed

text\<open>partJoin:\<close>

lemma partJoin_commute:
"partJoin P Q = partJoin Q P"
unfolding partJoin_def partGen_def
using Un_commute by metis

lemma Union_partJoin_L:
"Union P \<subseteq> Union (partJoin P Q)"
unfolding partJoin_def partGen_def by auto

lemma Union_partJoin_R:
"Union Q \<subseteq> Union (partJoin P Q)"
unfolding partJoin_def partGen_def by auto

lemma part_partJoin[simp]:
assumes "part I P" and "part I Q"
shows "part I (partJoin P Q)"
proof-
  have 1: "Union (P Un Q) = I"
  using assms unfolding part_def by auto
  show ?thesis using part_partGen[of "P Un Q"]
  unfolding 1 partJoin_def by auto
qed

lemma finer_partJoin_L[simp]:
assumes *: "part I P" and **: "part I Q"
shows "finer P (partJoin P Q)"
proof-
  have 1: "part I (partJoin P Q)" using assms by simp
  {fix J j assume J: "J \<in> partJoin P Q" and j: "j \<in> J"
   hence "J \<subseteq> I" using 1 by (metis Union_upper part_def)
   with j have "j \<in> I" by auto
   then obtain J' where jJ': "j \<in> J'" and J': "J' \<in> P"
   using * unfolding part_def by auto
   hence "J \<inter> J' \<noteq> {}" using j by auto
   moreover obtain J0 where "J = gen (P Un Q) J0"
   and "J0 \<in> P Un Q"
   using J unfolding partJoin_def partGen_def by blast
   ultimately have "J' \<subseteq> J"
   using J' gen_nchotomy[of J' "P Un Q" J0] by blast
   hence "j \<in> \<Union>{J' \<in> P. J' \<subseteq> J}" using J' jJ' by blast
  }
  thus ?thesis unfolding finer_def
  unfolding partJoin_def partGen_def by blast
qed

lemma finer_partJoin_R[simp]:
assumes *: "part I P" and **: "part I Q"
shows "finer Q (partJoin P Q)"
using assms finer_partJoin_L[of I Q P] partJoin_commute[of P Q] by auto

lemma finer_emp[simp]:
assumes "finer {} Q"
shows "Q \<subseteq> { {} }"
using assms unfolding finer_def by auto

text\<open>compat:\<close>

lemma part_emp_R[simp]:
"part I {} \<longleftrightarrow> I = {}"
unfolding part_def by auto

lemma part_emp_L[simp]:
"part {} P \<Longrightarrow> P \<subseteq> { {} }"
unfolding part_def by auto

lemma finite_partJoin[simp]:
assumes "finite P" and "finite Q"
shows "finite (partJoin P Q)"
using assms unfolding partJoin_def by auto

lemma emp_partJoin[simp]:
assumes "{} \<notin> P" and "{} \<notin> Q"
shows "{} \<notin> partJoin P Q"
using assms unfolding partJoin_def by auto

text\<open>partCompat:\<close>

lemma partCompat_Un[simp]:
"partCompat (P Un Q) theta f \<longleftrightarrow>
 partCompat P theta f \<and> partCompat Q theta f"
unfolding partCompat_def by auto

lemma partCompat_gen_aux:
assumes theta: "sym theta" "trans theta"
and fP: "partCompat P theta f" and I: "I \<in> P"
and i: "i \<in> I" and j: "j \<in> gen P I" and ij: "i \<noteq> j"
shows "(f i, f j) \<in> theta"
using j ij proof induct
  case (incl j)
  thus ?case
  using fP I i unfolding partCompat_def compat_def by blast
next
  case (ext J j0 j)
  show ?case
  proof(cases "i = j0")
    case False note case_i = False
    hence 1: "(f i, f j0) \<in> theta" using ext by blast
    show ?thesis
    proof(cases "j = j0")
      case True
      thus ?thesis using case_i 1 by simp
    next
      case False
      hence "(f j, f j0) \<in> theta" using \<open>j0 \<in> J\<close> \<open>j \<in> J\<close> \<open>J \<in> P\<close>
      using fP unfolding partCompat_def compat_def by auto
      hence "(f j0, f j) \<in> theta" using theta unfolding sym_def by simp
      thus ?thesis using 1 theta unfolding trans_def by blast
    qed
  next
    case True note case_i = True
    hence "j0 \<noteq> j" using \<open>i \<noteq> j\<close> by auto
    hence "(f j0, f j) \<in> theta" using \<open>j0 \<in> J\<close> \<open>j \<in> J\<close> \<open>J \<in> P\<close>
    using fP unfolding partCompat_def compat_def by auto
    thus ?thesis unfolding case_i .
  qed
qed

lemma partCompat_gen:
assumes theta: "sym theta" "trans theta"
and fP: "partCompat P theta f" and I: "I \<in> P"
shows "compat (gen P I) theta f"
unfolding compat_def proof clarify
  fix i j assume ij: "{i, j} \<subseteq> gen P I"  "i \<noteq> j"
  show "(f i, f j) \<in> theta"
  proof(cases "i \<in> I")
    case True note i = True
    show ?thesis
    proof(cases "j \<in> I")
      case True
      thus ?thesis using i ij I fP unfolding partCompat_def compat_def by blast
    next
      case False
      hence "i \<noteq> j" using i by auto
      thus ?thesis using assms partCompat_gen_aux i ij by auto
    qed
  next
    case False note i = False
    show ?thesis
    proof(cases "j \<in> I")
      case True
      hence "j \<noteq> i" using i by auto
      hence "(f j, f i) \<in> theta" using assms partCompat_gen_aux[of theta P f I j i] True ij by auto
      thus ?thesis using theta unfolding sym_def by auto
    next
      case False note j = False
      show ?thesis
      proof(cases "I = {}")
        case True
        hence False using ij by simp
        thus ?thesis by simp
      next
        case False
        then obtain i0 where i0: "i0 \<in> I" by auto
        hence i0_not: "i0 \<notin> {i,j}" using i j by auto
        have "(f i0, f i) \<in> theta"
        using assms i0 i0_not ij partCompat_gen_aux[of theta P f I i0 i] by blast
        hence "(f i, f i0) \<in> theta" using theta unfolding sym_def by auto
        moreover have "(f i0, f j) \<in> theta"
        using assms i0 i0_not ij partCompat_gen_aux[of theta P f I i0 j] by blast
        ultimately show ?thesis using theta unfolding trans_def by blast
      qed
    qed
  qed
qed

lemma partCompat_partGen:
assumes "sym theta" and "trans theta"
and "partCompat P theta f"
shows "partCompat (partGen P) theta f"
unfolding partCompat_def partGen_def
using assms partCompat_gen[of theta P f] by auto

lemma partCompat_partJoin[simp]:
assumes "sym theta" and "trans theta"
and "partCompat P theta f" and "partCompat Q theta f"
shows "partCompat (partJoin P Q) theta f"
by (metis assms partCompat_Un partCompat_partGen partJoin_def)

text\<open>lift:\<close>

lemma inj_on_lift:
assumes P: "part I0 P" and Q: "part I0 Q" and PQ: "finer P Q"
and F: "inj_on F P" and FP: "part J0 (F ` P)" and emp: "{} \<notin> F ` P"
shows "inj_on (lift P F) Q"
unfolding inj_on_def proof clarify
  fix II II' assume II: "II \<in> Q" and II': "II' \<in> Q" and eq: "lift P F II = lift P F II'"
  have 1: "II = Union {I \<in> P . I \<subseteq> II}" using PQ II unfolding finer_def by auto
  have 2: "II' = Union {I \<in> P . I \<subseteq> II'}" using PQ II' unfolding finer_def by auto
  {fix I
   assume I: "I \<in> P"  "I \<subseteq> II"
   hence "F I \<subseteq> lift P F II" unfolding lift_def[abs_def] by blast
   hence 3: "F I \<subseteq> lift P F II'" unfolding eq .
   have "F I \<noteq> {}" using emp I FP by auto
   then obtain j where j: "j \<in> F I" by auto
   with 3 obtain I' where I': "I' \<in> P \<and> I' \<subseteq> II'" and "j \<in> F I'" unfolding lift_def [abs_def] by auto
   hence "F I Int F I' \<noteq> {}" using j by auto
   hence "F I = F I'" using FP I I' unfolding part_def by auto
   hence "I = I'" using F I I' unfolding inj_on_def by auto
   hence "I \<subseteq> II'" using I' by auto
  }
  hence a: "II \<subseteq> II'" using 1 2 by blast
  (*  *)
  {fix I
   assume I: "I \<in> P"  "I \<subseteq> II'"
   hence "F I \<subseteq> lift P F II'" unfolding lift_def [abs_def] by blast
   hence 3: "F I \<subseteq> lift P F II" unfolding eq .
   have "F I \<noteq> {}" using emp I FP by auto
   then obtain j where j: "j \<in> F I" by auto
   with 3 obtain I' where I': "I' \<in> P \<and> I' \<subseteq> II" and "j \<in> F I'" unfolding lift_def [abs_def] by auto
   hence "F I Int F I' \<noteq> {}" using j by auto
   hence "F I = F I'" using FP I I' unfolding part_def by auto
   hence "I = I'" using F I I' unfolding inj_on_def by auto
   hence "I \<subseteq> II" using I' by auto
  }
  hence "II' \<subseteq> II" using 1 2 by blast
  with a show "II = II'" by auto
qed

lemma part_lift:
assumes P: "part I0 P" and Q: "part I0 Q" and PQ: "finer P Q"
and F: "inj_on F P" and FP: "part J0 (F ` P)" and emp: "{} \<notin> P" "{} \<notin> F ` P"
shows "part J0 (lift P F ` Q)"
unfolding part_def proof (intro conjI allI impI)
  show "\<Union>(lift P F ` Q) = J0"
  proof safe
    fix j II assume "j \<in> lift P F II" and II: "II \<in> Q"
    then obtain I where "j \<in> F I" and "I \<in> P" and "I \<subseteq> II"
    unfolding lift_def by auto
    thus "j \<in> J0" using FP unfolding part_def by auto
  next
    fix j assume "j \<in> J0"
    then obtain J where J: "J \<in> F ` P" and j: "j \<in> J" using FP unfolding part_def by auto
    define I where "I = inv_into P F J"
    have j: "j \<in> F I" unfolding I_def using j J F by auto
    have I: "I \<in> P" unfolding I_def using F J by auto
    obtain II where "I \<subseteq> II" and "II \<in> Q" using P Q PQ I finer_ex[of I0 P Q I] by auto
    thus "j \<in> \<Union> (lift P F ` Q)" unfolding lift_def [abs_def] using j I by auto
  qed
next
  fix JJ1 JJ2 assume JJ12: "JJ1 \<in> lift P F ` Q \<and> JJ2 \<in> lift P F ` Q \<and> JJ1 \<noteq> JJ2"
  then obtain II1 II2 where II12: "{II1,II2} \<subseteq> Q" and JJ1: "JJ1 = lift P F II1"
  and JJ2: "JJ2 = lift P F II2" by auto
  have "II1 \<noteq> II2" using JJ12 unfolding JJ1 JJ2 using II12 assms
  using inj_on_lift[of I0 P Q F] by auto
  hence 4: "II1 Int II2 = {}" using II12 Q unfolding part_def by auto
  show "JJ1 \<inter> JJ2 = {}"
  proof(rule ccontr)
    assume "JJ1 \<inter> JJ2 \<noteq> {}"
    then obtain j where j: "j \<in> JJ1" "j \<in> JJ2" by auto
    from j obtain I1 where "j \<in> F I1" and I1: "I1 \<in> P" "I1 \<subseteq> II1"
    unfolding JJ1 lift_def [abs_def] by auto
    moreover from j obtain I2 where "j \<in> F I2" and I2: "I2 \<in> P" "I2 \<subseteq> II2"
    unfolding JJ2 lift_def [abs_def] by auto
    ultimately have "F I1 Int F I2 \<noteq> {}" by blast
    hence "F I1 = F I2" using I1 I2 FP unfolding part_def by blast
    hence "I1 = I2" using I1 I2 F unfolding inj_on_def by auto
    moreover have "I1 \<noteq> {}" using I1 emp by auto
    ultimately have "II1 Int II2 \<noteq> {}" using I1 I2 by auto
    thus False using 4 by simp
  qed
qed

lemma finer_lift:
assumes "finer P Q"
shows "finer (F ` P) (lift P F ` Q)"
unfolding finer_def proof (intro conjI ballI impI)
  fix JJ assume JJ: "JJ \<in> lift P F ` Q"
  show "JJ = \<Union> {J \<in> F ` P. J \<subseteq> JJ}"
  proof safe
    fix j assume j: "j \<in> JJ"
    obtain II where II: "II \<in> Q" and JJ: "JJ = lift P F II" using JJ by auto
    then obtain I where j: "j \<in> F I" and I: "I \<in> P \<and> I \<subseteq> II" and "F I \<subseteq> JJ"
    using j unfolding lift_def [abs_def] by auto
    thus "j \<in> \<Union>{J \<in> F ` P. J \<subseteq> JJ}" using I j by auto
  qed auto
next
  assume "F ` P \<noteq> {}"
  thus "lift P F ` Q \<noteq> {}"
  using assms unfolding lift_def [abs_def] finer_def by simp
qed


subsection \<open>Basic setting for bisimilarity\<close>

locale PL_Indis =
  PL aval tval cval
  for aval :: "'atom \<Rightarrow> 'state \<Rightarrow> 'state" and
      tval :: "'test \<Rightarrow> 'state \<Rightarrow> bool" and
      cval :: "'choice \<Rightarrow> 'state \<Rightarrow> real" +
  fixes
    indis :: "'state rel"
  assumes
    equiv_indis: "equiv UNIV indis"


(*******************************************)
context PL_Indis
begin

abbreviation indisAbbrev (infix "\<approx>" 50)
where "s1 \<approx> s2 \<equiv> (s1, s2) \<in> indis"

lemma refl_indis: "refl indis"
and trans_indis: "trans indis"
and sym_indis: "sym indis"
using equiv_indis unfolding equiv_def by auto

lemma indis_refl[intro]: "s \<approx> s"
using refl_indis unfolding refl_on_def by simp

lemma indis_trans[trans]: "\<lbrakk>s \<approx> s'; s' \<approx> s''\<rbrakk> \<Longrightarrow> s \<approx> s''"
using trans_indis unfolding trans_def by blast

lemma indis_sym[sym]: "s \<approx> s' \<Longrightarrow> s' \<approx> s"
using sym_indis unfolding sym_def by blast


subsection\<open>Discreetness\<close>

coinductive discr where
intro:
"(\<And> s i. i < brn c \<longrightarrow> s \<approx> eff c s i \<and> discr (cont c s i))
 \<Longrightarrow> discr c"

definition discrL where
"discrL cl \<equiv> \<forall> c \<in> set cl. discr c"

lemma discrL_intro[intro]:
assumes "\<And> c. c \<in> set cl \<Longrightarrow> discr c"
shows "discrL cl"
using assms unfolding discrL_def by auto

lemma discrL_discr[simp]:
assumes "discrL cl" and "c \<in> set cl"
shows "discr c"
using assms unfolding discrL_def by simp

lemma discrL_update[simp]:
assumes cl: "discrL cl" and c': "discr c'"
shows "discrL (cl[n := c'])"
proof(cases "n < length cl")
  case True
  show ?thesis
  unfolding discrL_def proof safe
    fix c assume "c \<in> set (cl[n := c'])"
    hence "c \<in> insert c' (set cl)" using set_update_subset_insert by fastforce
    thus "discr c" using assms by (cases "c = c'") auto
  qed
qed (insert cl, auto)

text\<open>Coinduction for discreetness:\<close>

lemma discr_coind[consumes 1, case_names Hyp, induct pred: discr]:
assumes *: "phi c" and
**: "\<And> c s i. \<lbrakk> phi c ; i < brn c\<rbrakk>
       \<Longrightarrow> s \<approx> eff c s i \<and> (phi (cont c s i) \<or> discr (cont c s i))"
shows "discr c"
using * apply(induct rule: discr.coinduct) using ** by auto

lemma discr_raw_coind[consumes 1, case_names Hyp]:
assumes *: "phi c" and
**: "\<And> c s i. \<lbrakk>i < brn c; phi c\<rbrakk> \<Longrightarrow> s \<approx> eff c s i \<and> phi (cont c s i)"
shows "discr c"
using * apply(induct) using ** by blast

text\<open>Discreetness versus transition:\<close>

lemma discr_cont[simp]:
assumes *: "discr c" and **: "i < brn c"
shows "discr (cont c s i)"
using * apply(cases rule: discr.cases) using ** by blast

lemma discr_eff_indis[simp]:
assumes *: "discr c" and **: "i < brn c"
shows "s \<approx> eff c s i"
using * apply(cases rule: discr.cases) using ** by blast


subsection\<open>Self-isomorphism\<close>

coinductive siso where
intro:
"\<lbrakk>\<And> s i. i < brn c \<Longrightarrow> siso (cont c s i);
  \<And> s t i.
     i < brn c \<and> s \<approx> t \<Longrightarrow>
     eff c s i \<approx> eff c t i \<and> wt c s i = wt c t i \<and> cont c s i = cont c t i\<rbrakk>
  \<Longrightarrow> siso c"

definition sisoL where
"sisoL cl \<equiv> \<forall> c \<in> set cl. siso c"

lemma sisoL_intro[intro]:
assumes "\<And> c. c \<in> set cl \<Longrightarrow> siso c"
shows "sisoL cl"
using assms unfolding sisoL_def by auto

lemma sisoL_siso[simp]:
assumes "sisoL cl" and "c \<in> set cl"
shows "siso c"
using assms unfolding sisoL_def by simp

lemma sisoL_update[simp]:
assumes cl: "sisoL cl" and c': "siso c'"
shows "sisoL (cl[n := c'])"
proof(cases "n < length cl")
  case True
  show ?thesis
  unfolding sisoL_def proof safe
    fix c assume "c \<in> set (cl[n := c'])"
    hence "c \<in> insert c' (set cl)" using set_update_subset_insert by fastforce
    thus "siso c" using assms by (cases "c = c'") auto
  qed
qed (insert cl, auto)

text\<open>Coinduction for self-isomorphism:\<close>

lemma siso_coind[consumes 1, case_names Obs Cont, induct pred: siso]:
assumes *: "phi c" and
**: "\<And> c s t i. \<lbrakk>i < brn c; phi c; s \<approx> t\<rbrakk> \<Longrightarrow>
                 eff c s i \<approx> eff c t i \<and> wt c s i = wt c t i \<and> cont c s i = cont c t i" and
***: "\<And> c s i. \<lbrakk>i < brn c; phi c\<rbrakk> \<Longrightarrow> phi (cont c s i) \<or> siso (cont c s i)"
shows "siso c"
using * apply(induct rule: siso.coinduct) using ** *** by auto

lemma siso_raw_coind[consumes 1, case_names Obs Cont]:
assumes *: "phi c" and
***: "\<And> c s t i. \<lbrakk>i < brn c; phi c; s \<approx> t\<rbrakk> \<Longrightarrow>
                  eff c s i \<approx> eff c t i \<and> wt c s i = wt c t i \<and> cont c s i = cont c t i" and
**: "\<And> c s i. \<lbrakk>i < brn c; phi c\<rbrakk> \<Longrightarrow> phi (cont c s i)"
shows "siso c"
using * apply induct using ** *** by blast+

text\<open>Self-Isomorphism versus transition:\<close>

lemma siso_cont[simp]:
assumes *: "siso c" and **: "i < brn c"
shows "siso (cont c s i)"
using * apply(cases rule: siso.cases) using ** by blast

lemma siso_cont_indis[simp]:
assumes *: "siso c" and **: "s \<approx> t" "i < brn c"
shows "eff c s i \<approx> eff c t i \<and> wt c s i = wt c t i \<and> cont c s i = cont c t i"
using * apply(cases rule: siso.cases) using ** by blast


subsection\<open>Notions of bisimilarity\<close>

text\<open>Matchers\<close>

(* The notations are essentially the ones from the paper, except that,
   instead the paper's "Q" (which is redundant), we write "F P".
   Also, for the proper management of the proof, we have some intermediate
   predicates that compose the matchers.
*)

definition mC_C_part where
"mC_C_part c d P F \<equiv>
 {} \<notin> P \<and> {} \<notin> F ` P \<and>
 part {..< brn c} P \<and> part {..< brn d} (F ` P)"

definition mC_C_wt where
"mC_C_wt c d s t P F \<equiv> \<forall> I \<in> P. sum (wt c s) I = sum (wt d t) (F I)"

definition mC_C_eff_cont where
"mC_C_eff_cont theta c d s t P F \<equiv>
 \<forall> I i j.
   I \<in> P \<and> i \<in> I \<and> j \<in> F I \<longrightarrow>
   eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> theta"

definition mC_C where
"mC_C theta c d s t P F \<equiv>
 mC_C_part c d P F \<and> inj_on F P \<and> mC_C_wt c d s t P F \<and> mC_C_eff_cont theta c d s t P F"

definition matchC_C where
"matchC_C theta c d \<equiv> \<forall> s t. s \<approx> t \<longrightarrow> (\<exists> P F. mC_C theta c d s t P F)"

(*  *)
definition mC_ZOC_part where
"mC_ZOC_part c d s t I0 P F \<equiv>
 {} \<notin> P - {I0} \<and> {} \<notin> F ` (P - {I0}) \<and> I0 \<in> P \<and>
 part {..< brn c} P \<and> part {..< brn d} (F ` P)"

definition mC_ZOC_wt where
"mC_ZOC_wt c d s t I0 P F \<equiv>
 sum (wt c s) I0 < 1 \<and> sum (wt d t) (F I0) < 1 \<longrightarrow>
 (\<forall> I \<in> P - {I0}.
    sum (wt c s) I / (1 - sum (wt c s) I0) =
    sum (wt d t) (F I) / (1 - sum (wt d t) (F I0)))"
(* Note: In case either sum is 1, the above condition
   holds vacously. *)

definition mC_ZOC_eff_cont0 where
"mC_ZOC_eff_cont0 theta c d s t I0 F \<equiv>
 (\<forall> i \<in> I0. s \<approx> eff c s i \<and> (cont c s i, d) \<in> theta) \<and>
 (\<forall> j \<in> F I0. t \<approx> eff d t j \<and> (c, cont d t j) \<in> theta)"

definition mC_ZOC_eff_cont where
"mC_ZOC_eff_cont theta c d s t I0 P F \<equiv>
 \<forall> I i j.
   I \<in> P - {I0} \<and> i \<in> I \<and> j \<in> F I \<longrightarrow>
   eff c s i \<approx> eff d t j \<and>
   (cont c s i, cont d t j) \<in> theta"

definition mC_ZOC where
"mC_ZOC theta c d s t I0 P F \<equiv>
 mC_ZOC_part c d s t I0 P F \<and>
 inj_on F P \<and>
 mC_ZOC_wt c d s t I0 P F \<and>
 mC_ZOC_eff_cont0 theta c d s t I0 F \<and>
 mC_ZOC_eff_cont theta c d s t I0 P F"

definition matchC_LC where
"matchC_LC theta c d \<equiv>
 \<forall> s t. s \<approx> t \<longrightarrow> (\<exists> I0 P F. mC_ZOC theta c d s t I0 P F)"

lemmas m_defs = mC_C_def mC_ZOC_def

lemmas m_defsAll =
mC_C_def mC_C_part_def mC_C_wt_def mC_C_eff_cont_def
mC_ZOC_def mC_ZOC_part_def mC_ZOC_wt_def mC_ZOC_eff_cont0_def mC_ZOC_eff_cont_def

lemmas match_defs =
matchC_C_def matchC_LC_def

lemma mC_C_mono:
assumes "mC_C theta c d s t P F" and "theta \<subseteq> theta'"
shows "mC_C theta' c d s t P F"
using assms unfolding m_defsAll by fastforce+

lemma matchC_C_mono:
assumes "matchC_C theta c d" and "theta \<subseteq> theta'"
shows "matchC_C theta' c d"
using assms mC_C_mono unfolding matchC_C_def by blast

lemma mC_ZOC_mono:
assumes "mC_ZOC theta c d s t I0 P F" and "theta \<subseteq> theta'"
shows "mC_ZOC theta' c d s t I0 P F"
using assms unfolding m_defsAll subset_eq by auto

lemma matchC_LC_mono:
assumes "matchC_LC theta c d" and "theta \<subseteq> theta'"
shows "matchC_LC theta' c d"
using assms mC_ZOC_mono unfolding matchC_LC_def
by metis

lemma Int_not_in_eq_emp:
"P \<inter> {I. I \<notin> P} = {}"
by blast

lemma mC_C_mC_ZOC:
assumes "mC_C theta c d s t P F"
shows "mC_ZOC theta c d s t {} (P Un { {} }) (%I. if I \<in> P then F I else {})"
(is "mC_ZOC theta c d s t ?I0 ?Q ?G")
unfolding mC_ZOC_def proof(intro conjI)
  show "mC_ZOC_part c d s t ?I0 ?Q ?G"
  unfolding mC_ZOC_part_def using assms unfolding mC_C_def mC_C_part_def
  by (auto simp add: Int_not_in_eq_emp)
next
  show "inj_on ?G ?Q"
  unfolding inj_on_def proof clarify
    fix I1 I2 assume I12: "I1 \<in> ?Q" "I2 \<in> ?Q"
    and G: "?G I1 = ?G I2"
    show "I1 = I2"
    proof(cases "I1 \<in> P")
      case True
      hence I2: "I2 \<in> P" apply(rule_tac ccontr)
      using G assms unfolding mC_C_def mC_C_part_def by auto
      with True G have "F I1 = F I2" by simp
      thus ?thesis using True I2 I12 assms unfolding mC_C_def inj_on_def by blast
    next
      case False note case1 = False
      hence I1: "I1 = {}" using I12 by blast
      show ?thesis
      proof(cases "I2 \<in> P")
        case False
        hence "I2 = {}" using I12 by blast
        thus ?thesis using I1 by blast
      next
        case True
        hence "I1 \<in> P" apply(rule_tac ccontr)
        using G assms unfolding mC_C_def mC_C_part_def by auto
        thus ?thesis using case1 by simp
      qed
    qed
  qed
qed(insert assms, unfold m_defsAll, fastforce+)

lemma matchC_C_matchC_LC:
assumes "matchC_C theta c d"
shows "matchC_LC theta c d"
using assms mC_C_mC_ZOC unfolding match_defs by blast


text\<open>Retracts:\<close>

(* Strong retract: *)
definition Sretr where
"Sretr theta \<equiv>
 {(c, d). matchC_C theta c d}"

(* Zero-One retract: *)
definition ZOretr where
"ZOretr theta \<equiv>
 {(c,d). matchC_LC theta c d}"

lemmas Retr_defs =
Sretr_def
ZOretr_def

lemma mono_Retr:
"mono Sretr"
"mono ZOretr"
unfolding mono_def Retr_defs
by (auto simp add: matchC_C_mono matchC_LC_mono)

lemma Retr_incl:
"Sretr theta \<subseteq> ZOretr theta"
unfolding Retr_defs
using matchC_C_matchC_LC by blast+


text\<open>The associated bisimilarity relations:\<close>

definition Sbis where "Sbis \<equiv> gfp Sretr"
definition ZObis where "ZObis \<equiv> gfp ZOretr"

abbreviation Sbis_abbrev (infix "\<approx>s" 55) where "c \<approx>s d \<equiv> (c, d) : Sbis"
abbreviation ZObis_abbrev (infix "\<approx>01" 55) where "c \<approx>01 d \<equiv> (c, d) : ZObis"

lemmas bis_defs = Sbis_def ZObis_def

(* Inclusions between bisimilarities: *)
lemma bis_incl:
"Sbis \<le> ZObis"
unfolding bis_defs
using Retr_incl gfp_mono by blast+

lemma bis_imp[simp]:
"\<And> c1 c2. c1 \<approx>s c2 \<Longrightarrow> c1 \<approx>01 c2"
using bis_incl unfolding bis_defs by auto

(*  Sbis: *)

lemma Sbis_prefix:
"Sbis \<le> Sretr Sbis"
unfolding Sbis_def
using def_gfp_unfold mono_Retr(1) by blast

lemma Sbis_fix:
"Sretr Sbis = Sbis"
unfolding Sbis_def
by (metis def_gfp_unfold mono_Retr(1))

lemma Sbis_mC_C:
assumes "c \<approx>s d" and "s \<approx> t"
shows "\<exists>P F. mC_C Sbis c d s t P F"
using assms Sbis_prefix unfolding Sretr_def matchC_C_def by auto

lemma Sbis_coind:
assumes "theta \<le> Sretr (theta Un Sbis)"
shows "theta \<le> Sbis"
using assms unfolding Sbis_def
by (metis Sbis_def assms def_coinduct mono_Retr(1))

lemma Sbis_raw_coind:
assumes "theta \<le> Sretr theta"
shows "theta \<le> Sbis"
proof-
  have "Sretr theta \<subseteq> Sretr (theta Un Sbis)"
  by (metis Un_upper1 monoD mono_Retr(1))
  hence "theta \<subseteq> Sretr (theta Un Sbis)" using assms by blast
  thus ?thesis using Sbis_coind by blast
qed

(* Symmetry *)

lemma mC_C_sym:
assumes "mC_C theta c d s t P F"
shows "mC_C (theta ^-1) d c t s (F ` P) (inv_into P F)"
unfolding mC_C_def proof (intro conjI)
  show "mC_C_eff_cont (theta\<inverse>) d c t s (F ` P) (inv_into P F)"
  unfolding mC_C_eff_cont_def proof clarify
    fix i j I
    assume I: "I \<in> P" and j: "j \<in> F I" and "i \<in> inv_into P F (F I)"
    hence "i \<in> I" using assms unfolding mC_C_def by auto
    hence "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> theta"
    using assms I j unfolding mC_C_def mC_C_eff_cont_def by auto
    thus "eff d t j \<approx> eff c s i \<and> (cont d t j, cont c s i) \<in> theta\<inverse>"
    by (metis converseI indis_sym)
  qed
qed(insert assms, unfold m_defsAll, auto)

lemma matchC_C_sym:
assumes "matchC_C theta c d"
shows "matchC_C (theta ^-1) d c"
unfolding matchC_C_def proof clarify
  fix t s
  assume "t \<approx> s"  hence "s \<approx> t" by (metis indis_sym)
  then obtain P F where "mC_C theta c d s t P F"
  using assms unfolding matchC_C_def by blast
  hence "mC_C (theta\<inverse>) d c t s (F ` P) (inv_into P F)"
  using mC_C_sym by auto
  thus "\<exists>Q G. mC_C (theta\<inverse>) d c t s Q G" by blast
qed

lemma Sretr_sym:
assumes "sym theta"
shows "sym (Sretr theta)"
unfolding sym_def proof clarify
  fix c d assume "(c, d) \<in> Sretr theta"
  hence "(d, c) \<in> Sretr (theta ^-1)"
  unfolding Sretr_def using matchC_C_sym by simp
  thus "(d, c) \<in> Sretr theta"
  using assms by (metis sym_conv_converse_eq)
qed

lemma sym_Sbis: "sym Sbis"
by (metis Sbis_def Sretr_sym mono_Retr(1) sym_gfp)

lemma Sbis_sym: "c \<approx>s d \<Longrightarrow> d \<approx>s c"
using sym_Sbis unfolding sym_def by blast


(* Transitivity: *)

lemma mC_C_trans:
assumes *: "mC_C theta1 c d s t P F" and **: "mC_C theta2 d e t u (F ` P) G"
shows "mC_C (theta1 O theta2) c e s u P (G o F)"
unfolding mC_C_def proof (intro conjI)
  show "mC_C_part c e P (G \<circ> F)"
  using assms unfolding mC_C_def mC_C_part_def by (auto simp add: image_comp)
next
  show "inj_on (G \<circ> F) P"
  using assms unfolding mC_C_def by (auto simp add: comp_inj_on)
next
  show "mC_C_eff_cont (theta1 O theta2) c e s u P (G \<circ> F)"
  unfolding mC_C_eff_cont_def proof clarify
    fix I i k
    assume I: "I \<in> P" and i: "i \<in> I" and k: "k \<in> (G \<circ> F) I"
    have "F I \<noteq> {}" using * I unfolding mC_C_def mC_C_part_def by auto
    then obtain j where j: "j \<in> F I" by auto
    have "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> theta1"
    using I i j * unfolding mC_C_def mC_C_eff_cont_def by auto
    moreover
    have "eff d t j \<approx> eff e u k \<and> (cont d t j, cont e u k) \<in> theta2"
    using I j k ** unfolding mC_C_def mC_C_eff_cont_def by auto
    ultimately
    show "eff c s i \<approx> eff e u k \<and> (cont c s i, cont e u k) \<in> theta1 O theta2"
    using indis_trans by blast
  qed
qed(insert assms, unfold m_defsAll, auto)

lemma mC_C_finer:
assumes *: "mC_C theta c d s t P F"
and theta: "trans theta"
and Q: "finer P Q" "finite Q" "{} \<notin> Q" "part {..<brn c} Q"
and c: "partCompat Q indis (eff c s)" "partCompat Q theta (cont c s)"
shows "mC_C theta c d s t Q (lift P F)"
unfolding mC_C_def proof (intro conjI)
  show "mC_C_part c d Q (lift P F)"
  unfolding mC_C_part_def proof(intro conjI)
    show "{} \<notin> lift P F ` Q" unfolding lift_def [abs_def] proof clarify
     fix II assume 1: "{} = \<Union>{F I |I. I \<in> P \<and> I \<subseteq> II}" and II: "II \<in> Q"
      hence "II \<noteq> {}" using Q by auto
      then obtain I where I: "I \<in> P" and "I \<subseteq> II"
      using Q II unfolding finer_def by blast
      hence "F I = {}" using 1 by auto
      thus False using * I unfolding mC_C_def mC_C_part_def by auto
    qed
  next
    show "part {..<brn d} (lift P F ` Q)"
    using Q * part_lift[of "{..<brn c}" P Q F "{..<brn d}"]
    unfolding mC_C_def mC_C_part_def by auto
  qed (insert Q, auto)
next
  show "inj_on (lift P F) Q"
  using Q * inj_on_lift[of "{..<brn c}" P Q F "{..<brn d}"]
  unfolding mC_C_def mC_C_part_def by auto
next
  show "mC_C_wt c d s t Q (lift P F)"
  unfolding mC_C_wt_def proof clarify
    fix II assume II: "II \<in> Q"
    define S where "S = {I \<in> P . I \<subseteq> II}"
    have II: "II = (UN I : S . id I)" using II Q unfolding finer_def S_def by auto
    have S: "\<And> I J. \<lbrakk>I : S; J : S; I \<noteq> J\<rbrakk> \<Longrightarrow> id I Int id J = {}" "finite S"
    unfolding S_def using * finite_part[of "{..<brn c}" P] unfolding mC_C_def mC_C_part_def part_def by auto
    have SS: "\<forall>I\<in>S. finite I" "\<forall>i\<in>S. finite (F i)"
    unfolding S_def using * unfolding mC_C_def mC_C_part_def part_def apply simp_all
    apply (metis complete_lattice_class.Sup_upper finite_lessThan finite_subset)
    by (metis finite_UN finite_UnionD finite_lessThan)
    have SSS: "\<forall>i\<in>S. \<forall>j\<in>S. i \<noteq> j \<longrightarrow> F i \<inter> F j = {}"
    proof clarify
      fix I J assume "I \<in> S" and "J \<in> S" and diff: "I \<noteq> J"
      hence IJ: "{I,J} \<subseteq> P" unfolding S_def by simp
      hence "F I \<noteq> F J" using * diff unfolding mC_C_def inj_on_def by auto
      thus "F I \<inter> F J = {}" using * IJ unfolding mC_C_def mC_C_part_def part_def by auto
    qed
    have "sum (wt c s) II = sum (sum (wt c s)) S"
    unfolding II using S SS sum.UNION_disjoint[of S id "wt c s"] by simp
    also have "... = sum (% I. sum (wt d t) (F I)) S"
    apply(rule sum.cong)
    using S apply force
    unfolding S_def using * unfolding mC_C_def mC_C_part_def mC_C_wt_def by auto
    also have "... = sum (wt d t) (UN I : S . F I)"
    unfolding lift_def using S sum.UNION_disjoint[of S F "wt d t"] S SS SSS by simp
    also have "(UN I : S . F I) = lift P F II" unfolding lift_def S_def by auto
    finally show "sum (wt c s) II = sum (wt d t) (lift P F II)" .
  qed
next
  show "mC_C_eff_cont theta c d s t Q (lift P F)"
  unfolding mC_C_eff_cont_def proof clarify
    fix II i j
    assume II: "II \<in> Q" and i: "i \<in> II" and "j \<in> lift P F II"
    then obtain I where j: "j \<in> F I" and I: "I \<in> P \<and> I \<subseteq> II" unfolding lift_def by auto
    hence "I \<noteq> {}" using * unfolding mC_C_def mC_C_part_def by auto
    then obtain i' where i': "i' \<in> I" by auto
    hence 1: "eff c s i' \<approx> eff d t j \<and> (cont c s i', cont d t j) \<in> theta"
    using * j I unfolding mC_C_def mC_C_eff_cont_def by auto
    show "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> theta"
    proof(cases "i' = i")
      case True show ?thesis using 1 unfolding True .
    next
      case False
      moreover have "i' \<in> II" using I i' by auto
      ultimately have "eff c s i \<approx> eff c s i' \<and> (cont c s i, cont c s i') \<in> theta"
      using i II c unfolding partCompat_def compat_def by auto
      thus ?thesis using 1 indis_trans theta unfolding trans_def by blast
    qed
  qed
qed

lemma mC_C_partCompat_eff:
assumes *: "mC_C theta c d s t P F"
shows "partCompat P indis (eff c s)"
unfolding partCompat_def compat_def proof clarify
  fix I i i' assume I: "I \<in> P" and ii': "{i, i'} \<subseteq> I" "i \<noteq> i'"
  hence "F I \<noteq> {}" using * unfolding m_defsAll by blast
  then obtain j where j: "j \<in> F I" by auto
  from ii' j I have 1: "eff c s i \<approx> eff d t j"
  using * unfolding m_defsAll by blast
  from ii' j I have 2: "eff c s i' \<approx> eff d t j"
  using * unfolding m_defsAll by blast
  from 1 2 show "eff c s i \<approx> eff c s i'"
  using indis_trans indis_sym by blast
qed

lemma mC_C_partCompat_cont:
assumes *: "mC_C theta c d s t P F"
and theta: "sym theta" "trans theta"
shows "partCompat P theta (cont c s)"
unfolding partCompat_def compat_def proof clarify
  fix I i i' assume I: "I \<in> P" and ii': "{i, i'} \<subseteq> I" "i \<noteq> i'"
  hence "F I \<noteq> {}" using * unfolding m_defsAll by blast
  then obtain j where j: "j \<in> F I" by auto
  from ii' j I have 1: "(cont c s i, cont d t j) \<in> theta"
  using * unfolding m_defsAll by blast
  from ii' j I have 2: "(cont c s i', cont d t j) \<in> theta"
  using * unfolding m_defsAll by blast
  from 1 2 show "(cont c s i, cont c s i')  \<in> theta"
  using theta unfolding trans_def sym_def by blast
qed

lemma matchC_C_sym_trans:
assumes *: "matchC_C theta c1 c" and **: "matchC_C theta c c2"
and theta: "sym theta" "trans theta"
shows "matchC_C theta c1 c2"
unfolding matchC_C_def proof clarify
  fix s1 s2 assume s1s2: "s1 \<approx> s2"
  define s where "s = s1"
  have s: "s \<approx> s1 \<and> s \<approx> s2" unfolding s_def using s1s2 by auto
  have th: "theta ^-1 = theta" "theta O theta \<subseteq> theta" using theta
  by (metis sym_conv_converse_eq trans_O_subset)+
  hence *: "matchC_C theta c c1" by (metis * matchC_C_sym)
  from s * obtain P1 F1 where m1: "mC_C theta c c1 s s1 P1 F1"
  unfolding matchC_C_def by blast
  from s ** obtain P2 F2 where m2: "mC_C theta c c2 s s2 P2 F2"
  unfolding matchC_C_def by blast
  define P where "P = partJoin P1 P2"
  (*  *)
  have P:
  "finer P1 P \<and> finer P2 P \<and>
   finite P \<and> {} \<notin> P \<and> part {..< brn c} P"
  using m1 m2 finer_partJoin_L finite_partJoin emp_partJoin part_partJoin finite_part[of "{..< brn c}" P]
  unfolding P_def mC_C_def mC_C_part_def by force
  (*  *)
  have "mC_C theta c c1 s s1 P (lift P1 F1)"
  proof(rule mC_C_finer)
    show "partCompat P indis (eff c s)"
    unfolding P_def apply(rule partCompat_partJoin)
    using m1 m2 sym_indis trans_indis mC_C_partCompat_eff by auto
  next
    show "partCompat P theta (cont c s)"
    unfolding P_def apply(rule partCompat_partJoin)
    using m1 m2 theta mC_C_partCompat_cont by auto
  qed(insert P m1 theta, auto)
  hence A: "mC_C theta c1 c s1 s (lift P1 F1 ` P) (inv_into P (lift P1 F1))"
  using mC_C_sym[of theta c c1 s s1 P "lift P1 F1"] unfolding th by blast
  (*  *)
  have B: "mC_C theta c c2 s s2 P (lift P2 F2)"
  proof(rule mC_C_finer)
    show "partCompat P indis (eff c s)"
    unfolding P_def apply(rule partCompat_partJoin)
    using m1 m2 sym_indis trans_indis mC_C_partCompat_eff by auto
  next
    show "partCompat P theta (cont c s)"
    unfolding P_def apply(rule partCompat_partJoin)
    using m1 m2 theta mC_C_partCompat_cont by auto
  qed(insert P m2 theta, auto)
  (*  *)
  have "inj_on (lift P1 F1) P"
  apply(rule inj_on_lift) using m1 m2 P unfolding m_defsAll by auto
  hence "inv_into P (lift P1 F1) ` lift P1 F1 ` P = P"
  by (metis inj_on_inv_into)
  hence "mC_C (theta O theta) c1 c2 s1 s2 (lift P1 F1 ` P) (lift P2 F2 o (inv_into P (lift P1 F1)))"
  apply - apply(rule mC_C_trans[of theta c1 c s1 s _ _ theta c2 s2])
  using A B by auto
  hence "mC_C theta c1 c2 s1 s2 (lift P1 F1 ` P) (lift P2 F2 o (inv_into P (lift P1 F1)))"
  using th mC_C_mono by blast
  thus "\<exists>R H. mC_C theta c1 c2 s1 s2 R H" by blast
qed

lemma Sretr_sym_trans:
assumes "sym theta \<and> trans theta"
shows "trans (Sretr theta)"
unfolding trans_def proof clarify
  fix c d e assume "(c, d) \<in> Sretr theta" and "(d, e) \<in> Sretr theta"
  thus "(c, e) \<in> Sretr theta"
  unfolding Sretr_def using assms matchC_C_sym_trans by blast
qed

lemma trans_Sbis: "trans Sbis"
by (metis Sbis_def Sretr_sym Sretr_sym_trans mono_Retr sym_trans_gfp)

lemma Sbis_trans: "\<lbrakk>c \<approx>s d; d \<approx>s e\<rbrakk> \<Longrightarrow> c \<approx>s e"
using trans_Sbis unfolding trans_def by blast


(* ZObis: *)

lemma ZObis_prefix:
"ZObis \<le> ZOretr ZObis"
unfolding ZObis_def
using def_gfp_unfold mono_Retr(2) by blast

lemma ZObis_fix:
"ZOretr ZObis = ZObis"
unfolding ZObis_def
by (metis def_gfp_unfold mono_Retr(2))

lemma ZObis_mC_ZOC:
assumes "c \<approx>01 d" and "s \<approx> t"
shows "\<exists>I0  P F. mC_ZOC ZObis c d s t I0 P F"
using assms ZObis_prefix unfolding ZOretr_def matchC_LC_def by blast

lemma ZObis_coind:
assumes "theta \<le> ZOretr (theta Un ZObis)"
shows "theta \<le> ZObis"
using assms unfolding ZObis_def
by (metis ZObis_def assms def_coinduct mono_Retr(2))

lemma ZObis_raw_coind:
assumes "theta \<le> ZOretr theta"
shows "theta \<le> ZObis"
proof-
  have "ZOretr theta \<subseteq> ZOretr (theta Un ZObis)"
  by (metis Un_upper1 monoD mono_Retr)
  hence "theta \<subseteq> ZOretr (theta Un ZObis)" using assms by blast
  thus ?thesis using ZObis_coind by blast
qed

(* Symmetry *)

lemma mC_ZOC_sym:
assumes theta: "sym theta" and *: "mC_ZOC theta c d s t I0 P F"
shows "mC_ZOC theta d c t s (F I0) (F ` P) (inv_into P F)"
unfolding mC_ZOC_def proof (intro conjI)
  show "mC_ZOC_part d c t s (F I0) (F ` P) (inv_into P F)"
  unfolding mC_ZOC_part_def proof(intro conjI)
    have 0: "inj_on F P" "I0 \<in> P" using * unfolding mC_ZOC_def mC_ZOC_part_def by blast+
    have "inv_into P F ` (F ` P - {F I0}) = inv_into P F ` (F ` (P - {I0}))"
    using 0 inj_on_image_set_diff[of F P P "{I0}", OF _ Set.Diff_subset] by simp
    also have "... = P - {I0}" using 0 by (metis Diff_subset inv_into_image_cancel)
    finally have "inv_into P F ` (F ` P - {F I0}) = P - {I0}" .
    thus "{} \<notin> inv_into P F ` (F ` P - {F I0})"
    using * unfolding mC_ZOC_def mC_ZOC_part_def by simp
  (*  *)
    have "part {..<brn c} P" using * unfolding mC_ZOC_def mC_ZOC_part_def by blast
    thus "part {..<brn c} (inv_into P F ` F ` P)" using 0 by auto
  qed(insert *, unfold mC_ZOC_def mC_ZOC_part_def, blast+)
next
  have 0: "inj_on F P" "I0 \<in> P" using * unfolding mC_ZOC_def mC_ZOC_part_def by blast+
  show "mC_ZOC_wt d c t s (F I0) (F ` P) (inv_into P F)"
  unfolding mC_ZOC_wt_def proof(intro conjI ballI impI)
    fix J assume "J \<in> F ` P - {F I0}" and le_1: "sum (wt d t) (F I0) < 1 \<and> sum (wt c s) (inv_into P F (F I0)) < 1"
    then obtain I where I: "I \<in> P - {I0}" and J: "J = F I"
      by (metis image_iff member_remove remove_def)
    have 2: "inv_into P F J = I" unfolding J using 0 I by simp
    have 3: "inv_into P F (F I0) = I0" using 0 by simp
    show
    "sum (wt d t) J / (1 - sum (wt d t) (F I0)) =
     sum (wt c s) (inv_into P F J) / (1 - sum (wt c s) (inv_into P F (F I0)))"
    unfolding 2 3 unfolding J
    using * I le_1 unfolding mC_ZOC_def mC_ZOC_wt_def by (metis 3 J)
  qed
next
  show "mC_ZOC_eff_cont theta d c t s (F I0) (F ` P) (inv_into P F)"
  unfolding mC_ZOC_eff_cont_def proof(intro allI impI, elim conjE)
    fix i j J
    assume "J \<in> F ` P - {F I0}" and j: "j \<in> J" and i: "i \<in> inv_into P F J"
    then obtain I where J: "J = F I" and I: "I \<in> P - {I0}"
      by (metis image_iff member_remove remove_def)
    hence "i \<in> I" using assms i unfolding mC_ZOC_def by auto
    hence "eff c s i \<approx> eff d t j \<and> (cont c s i, cont d t j) \<in> theta"
    using assms I j unfolding mC_ZOC_def mC_ZOC_eff_cont_def J by auto
    thus "eff d t j \<approx> eff c s i \<and> (cont d t j, cont c s i) \<in> theta"
    by (metis assms indis_sym sym_def)
  qed
qed(insert assms, unfold sym_def m_defsAll, auto)

lemma matchC_LC_sym:
assumes *: "sym theta" and "matchC_LC theta c d"
shows "matchC_LC theta d c"
unfolding matchC_LC_def proof clarify
  fix t s
  assume "t \<approx> s"  hence "s \<approx> t" by (metis indis_sym)
  then obtain I0 P F where "mC_ZOC theta c d s t I0 P F"
  using assms unfolding matchC_LC_def by blast
  hence "mC_ZOC theta d c t s (F I0) (F ` P) (inv_into P F)"
  using mC_ZOC_sym * by auto
  thus "\<exists>I0 Q G. mC_ZOC theta d c t s I0 Q G" by blast
qed

lemma ZOretr_sym:
assumes "sym theta"
shows "sym (ZOretr theta)"
unfolding sym_def proof clarify
  fix c d assume "(c, d) \<in> ZOretr theta"
  hence "(d, c) \<in> ZOretr theta"
  unfolding ZOretr_def using assms matchC_LC_sym by simp
  thus "(d, c) \<in> ZOretr theta"
  using assms by (metis sym_conv_converse_eq)
qed

lemma sym_ZObis: "sym ZObis"
by (metis ZObis_def ZOretr_sym mono_Retr sym_gfp)

lemma ZObis_sym: "c \<approx>01 d \<Longrightarrow> d \<approx>01 c"
using sym_ZObis unfolding sym_def by blast


subsection \<open>List versions of the bisimilarities\<close>

(* For Sbis: *)

definition SbisL where
"SbisL cl dl \<equiv>
 length cl = length dl \<and> (\<forall> n < length cl. cl ! n \<approx>s dl ! n)"

lemma SbisL_intro[intro]:
assumes "length cl = length dl" and
"\<And> n. \<lbrakk>n < length cl; n < length dl\<rbrakk> \<Longrightarrow> cl ! n \<approx>s dl ! n"
shows "SbisL cl dl"
using assms unfolding SbisL_def by auto

lemma SbisL_length[simp]:
assumes "SbisL cl dl"
shows "length cl = length dl"
using assms unfolding SbisL_def by simp

lemma SbisL_Sbis[simp]:
assumes "SbisL cl dl" and "n < length cl \<or> n < length dl"
shows "cl ! n \<approx>s dl ! n"
using assms unfolding SbisL_def by simp

lemma SbisL_update[simp]:
assumes cldl: "SbisL cl dl" and c'd': "c' \<approx>s d'"
shows "SbisL (cl [n := c']) (dl [n := d'])" (is "SbisL ?cl' ?dl'")
proof(cases "n < length cl")
  case True
  show ?thesis proof
    fix m assume m: "m < length ?cl'" "m < length ?dl'"
    thus "?cl' ! m \<approx>s ?dl' ! m" using assms by (cases "m = n") auto
  qed (insert cldl, simp)
qed (insert cldl, simp)

lemma SbisL_update_L[simp]:
assumes "SbisL cl dl" and "c' \<approx>s dl!n"
shows "SbisL (cl[n := c']) dl"
proof-
  let ?d' = "dl!n"
  have "SbisL (cl[n := c']) (dl[n := ?d'])"
  apply(rule SbisL_update) using assms by auto
  thus ?thesis by simp
qed

lemma SbisL_update_R[simp]:
assumes "SbisL cl dl" and "cl!n \<approx>s d'"
shows "SbisL cl (dl[n := d'])"
proof-
  let ?c' = "cl!n"
  have "SbisL (cl[n := ?c']) (dl[n := d'])"
  apply(rule SbisL_update) using assms by auto
  thus ?thesis by simp
qed

(* For ZObis: *)

definition ZObisL where
"ZObisL cl dl \<equiv>
 length cl = length dl \<and> (\<forall> n < length cl. cl ! n \<approx>01 dl ! n)"

lemma ZObisL_intro[intro]:
assumes "length cl = length dl" and
"\<And> n. \<lbrakk>n < length cl; n < length dl\<rbrakk> \<Longrightarrow> cl ! n \<approx>01 dl ! n"
shows "ZObisL cl dl"
using assms unfolding ZObisL_def by auto

lemma ZObisL_length[simp]:
assumes "ZObisL cl dl"
shows "length cl = length dl"
using assms unfolding ZObisL_def by simp

lemma ZObisL_ZObis[simp]:
assumes "ZObisL cl dl" and "n < length cl \<or> n < length dl"
shows "cl ! n \<approx>01 dl ! n"
using assms unfolding ZObisL_def by simp

lemma ZObisL_update[simp]:
assumes cldl: "ZObisL cl dl" and c'd': "c' \<approx>01 d'"
shows "ZObisL (cl [n := c']) (dl [n := d'])" (is "ZObisL ?cl' ?dl'")
proof(cases "n < length cl")
  case True
  show ?thesis proof
    fix m assume m: "m < length ?cl'" "m < length ?dl'"
    thus "?cl' ! m \<approx>01 ?dl' ! m" using assms by (cases "m = n") auto
  qed (insert cldl, simp)
qed (insert cldl, simp)

lemma ZObisL_update_L[simp]:
assumes "ZObisL cl dl" and "c' \<approx>01 dl!n"
shows "ZObisL (cl[n := c']) dl"
proof-
  let ?d' = "dl!n"
  have "ZObisL (cl[n := c']) (dl[n := ?d'])"
  apply(rule ZObisL_update) using assms by auto
  thus ?thesis by simp
qed

lemma ZObisL_update_R[simp]:
assumes "ZObisL cl dl" and "cl!n \<approx>01 d'"
shows "ZObisL cl (dl[n := d'])"
proof-
  let ?c' = "cl!n"
  have "ZObisL (cl[n := ?c']) (dl[n := d'])"
  apply(rule ZObisL_update) using assms by auto
  thus ?thesis by simp
qed


subsection\<open>Discreetness for configurations\<close>

coinductive discrCf where
intro:
"(\<And> i. i < brn (fst cf) \<longrightarrow>
       snd cf \<approx> snd (cont_eff cf i) \<and> discrCf (cont_eff cf i))
 \<Longrightarrow> discrCf cf"

text\<open>Coinduction for discrness:\<close>

lemma discrCf_coind[consumes 1, case_names Hyp, induct pred: discr]:
assumes *: "phi cf" and
**: "\<And> cf i.
       \<lbrakk>i < brn (fst cf); phi cf\<rbrakk> \<Longrightarrow>
        snd cf \<approx> snd (cont_eff cf i) \<and> (phi (cont_eff cf i) \<or> discrCf (cont_eff cf i))"
shows "discrCf cf"
using * apply(induct rule: discrCf.coinduct) using ** by auto

lemma discrCf_raw_coind[consumes 1, case_names Hyp]:
assumes *: "phi cf" and
**: "\<And> cf i. \<lbrakk>i < brn (fst cf); phi cf\<rbrakk> \<Longrightarrow>
              snd cf \<approx> snd (cont_eff cf i) \<and> phi (cont_eff cf i)"
shows "discrCf cf"
using * apply(induct) using ** by blast

text\<open>Discreetness versus transition:\<close>

lemma discrCf_cont[simp]:
assumes *: "discrCf cf" and **: "i < brn (fst cf)"
shows "discrCf (cont_eff cf i)"
using * apply(cases rule: discrCf.cases) using ** by blast

lemma discrCf_eff_indis[simp]:
assumes *: "discrCf cf" and **: "i < brn (fst cf)"
shows "snd cf \<approx> snd (cont_eff cf i)"
using * apply(cases rule: discrCf.cases) using ** by blast

lemma discr_discrCf:
assumes "discr c"
shows "discrCf (c, s)"
proof-
  {fix cf :: "('test, 'atom, 'choice) cmd \<times> 'state"
   assume "discr (fst cf)"
   hence "discrCf cf"
   apply (induct)
   using discr_eff_indis discr_cont unfolding eff_def cont_def cont_eff_def by auto
  }
  thus ?thesis using assms by auto
qed

lemma ZObis_pres_discrCfL:
assumes "fst cf \<approx>01 fst df" and "snd cf \<approx> snd df" and "discrCf df"
shows "discrCf cf"
proof-
  have "\<exists> df. fst cf \<approx>01 fst df \<and> snd cf \<approx> snd df \<and> discrCf df" using assms by blast
  thus ?thesis
  proof (induct rule: discrCf_raw_coind)
    case (Hyp cf i)
    then obtain df where i: "i < brn (fst cf)" and
    df: "discrCf df" and cf_df: "fst cf \<approx>01 fst df" "snd cf \<approx> snd df" by blast
    then obtain I0 P F where
    match: "mC_ZOC ZObis (fst cf) (fst df) (snd cf) (snd df) I0 P F"
    using ZObis_mC_ZOC by blast
    hence "\<Union>P = {..<brn (fst cf)}"
    using i unfolding mC_ZOC_def mC_ZOC_part_def part_def by simp
    then obtain I where I: "I \<in> P" and i: "i \<in> I" using i by auto
    show ?case
    proof(cases "I = I0")
      case False
      then obtain j where j: "j \<in> F I" using match I False unfolding m_defsAll by blast
      hence "j < brn (fst df)" using I match
      unfolding mC_ZOC_def mC_ZOC_part_def part_def apply simp by blast
      hence md: "discrCf (cont_eff df j)" and s: "snd df \<approx> snd (cont_eff df j)"
      using df discrCf_cont[of df j] discrCf_eff_indis[of df j] by auto
      have 0: "snd (cont_eff cf i) \<approx> snd (cont_eff df j)" and
      md2: "fst (cont_eff cf i) \<approx>01 fst (cont_eff df j)"
      using I i j match False unfolding mC_ZOC_def mC_ZOC_eff_cont_def
      unfolding eff_def cont_def cont_eff_def by auto
      hence "snd cf \<approx> snd (cont_eff cf i)" using s indis_sym indis_trans cf_df by blast
      thus ?thesis using md md2 0 by blast
    next
      case True
      hence "snd cf \<approx> snd (cont_eff cf i) \<and> fst (cont_eff cf i) \<approx>01 fst df"
      using match i ZObis_sym unfolding mC_ZOC_def mC_ZOC_eff_cont0_def
      unfolding cont_eff_def cont_def eff_def by blast
      moreover have "snd (cont_eff cf i) \<approx> snd df"
      using match i indis_sym indis_trans cf_df unfolding mC_ZOC_def mC_ZOC_eff_cont0_def
      unfolding cont_eff_def cont_def eff_def True by blast
      ultimately show ?thesis using df cf_df by blast
    qed
  qed
qed

corollary ZObis_pres_discrCfR:
assumes "discrCf cf" and "fst cf \<approx>01 fst df" and "snd cf \<approx> snd df"
shows "discrCf df"
using assms ZObis_pres_discrCfL ZObis_sym indis_sym by blast


end (* context PL_Indis *)
(*******************************************)


end
