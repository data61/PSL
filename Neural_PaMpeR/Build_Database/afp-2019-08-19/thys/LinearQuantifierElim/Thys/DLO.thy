(*  Author:     Tobias Nipkow, 2007  *)

section "DLO"

theory DLO
imports QE Complex_Main
begin

subsection "Basics"

class dlo = linorder +
assumes dense: "x < z \<Longrightarrow> \<exists>y. x < y \<and> y < z"
and no_ub: "\<exists>u. x < u" and no_lb: "\<exists>l. l < x"

instance real :: dlo
proof
  fix r s :: real
  let ?v = "(r + s) / 2"
  assume "r < s"
  hence "r < ?v \<and> ?v < s" by simp
  thus "\<exists>v. r < v \<and> v < s" ..
next
  fix r :: real
  have "r < r + 1" by arith
  thus "\<exists>s. r < s" ..
next
  fix r :: real
  have "r - 1 < r" by arith
  thus "\<exists>s. s < r" ..
qed

datatype atom = Less nat nat | Eq nat nat

fun is_Less :: "atom \<Rightarrow> bool" where
"is_Less (Less i j) = True" |
"is_Less f = False"

abbreviation "is_Eq \<equiv> Not \<circ> is_Less"

lemma is_Less_iff: "is_Less a = (\<exists>i j. a = Less i j)"
by(cases a) auto
lemma is_Eq_iff: "(\<forall>i j. a \<noteq> Less i j) = (\<exists>i j. a = Eq i j)"
by(cases a) auto
lemma not_is_Eq_iff: "(\<forall>i j. a \<noteq> Eq i j) = (\<exists>i j. a = Less i j)"
by(cases a) auto

fun neg\<^sub>d\<^sub>l\<^sub>o :: "atom \<Rightarrow> atom fm" where
"neg\<^sub>d\<^sub>l\<^sub>o (Less i j) = Or (Atom(Less j i)) (Atom(Eq i j))" |
"neg\<^sub>d\<^sub>l\<^sub>o (Eq i j) = Or (Atom(Less i j)) (Atom(Less j i))"

fun I\<^sub>d\<^sub>l\<^sub>o :: "atom \<Rightarrow> 'a::dlo list \<Rightarrow> bool" where
"I\<^sub>d\<^sub>l\<^sub>o (Eq i j) xs = (xs!i = xs!j)" |
"I\<^sub>d\<^sub>l\<^sub>o (Less i j) xs = (xs!i < xs!j)"

fun depends\<^sub>d\<^sub>l\<^sub>o :: "atom \<Rightarrow> bool" where
"depends\<^sub>d\<^sub>l\<^sub>o(Eq i j) = (i=0 | j=0)" |
"depends\<^sub>d\<^sub>l\<^sub>o(Less i j) = (i=0 | j=0)"

fun decr\<^sub>d\<^sub>l\<^sub>o :: "atom \<Rightarrow> atom" where
"decr\<^sub>d\<^sub>l\<^sub>o (Less i j) = Less (i - 1) (j - 1)" |
"decr\<^sub>d\<^sub>l\<^sub>o (Eq i j) = Eq (i - 1) (j - 1)"

(* needed for code generation *)
definition [code del]: "nnf = ATOM.nnf neg\<^sub>d\<^sub>l\<^sub>o"
definition [code del]: "qelim = ATOM.qelim depends\<^sub>d\<^sub>l\<^sub>o decr\<^sub>d\<^sub>l\<^sub>o"
definition [code del]: "lift_dnf_qe = ATOM.lift_dnf_qe neg\<^sub>d\<^sub>l\<^sub>o depends\<^sub>d\<^sub>l\<^sub>o decr\<^sub>d\<^sub>l\<^sub>o"
definition [code del]: "lift_nnf_qe = ATOM.lift_nnf_qe neg\<^sub>d\<^sub>l\<^sub>o"

hide_const nnf qelim lift_dnf_qe lift_nnf_qe

lemmas DLO_code_lemmas = nnf_def qelim_def lift_dnf_qe_def lift_nnf_qe_def

interpretation DLO:
  ATOM neg\<^sub>d\<^sub>l\<^sub>o "(\<lambda>a. True)" I\<^sub>d\<^sub>l\<^sub>o depends\<^sub>d\<^sub>l\<^sub>o decr\<^sub>d\<^sub>l\<^sub>o
apply(unfold_locales)
apply(case_tac a)
apply simp_all
apply(case_tac a)
apply (simp_all add:linorder_class.not_less_iff_gr_or_eq
                    linorder_not_less linorder_neq_iff)
apply(case_tac a)
apply(simp_all add:nth_Cons')
done

lemmas [folded DLO_code_lemmas, code] =
  DLO.nnf.simps DLO.qelim_def DLO.lift_dnf_qe.simps DLO.lift_dnf_qe.simps

setup \<open>Sign.revert_abbrev "" @{const_abbrev DLO.I}\<close>

definition lbounds where "lbounds as = [i. Less (Suc i) 0 \<leftarrow> as]"
definition ubounds where "ubounds as = [i. Less 0 (Suc i) \<leftarrow> as]"
definition ebounds where
 "ebounds as = [i. Eq (Suc i) 0 \<leftarrow> as] @ [i. Eq 0 (Suc i) \<leftarrow> as]"

lemma set_lbounds: "set(lbounds as) = {i. Less (Suc i) 0 \<in> set as}"
by(auto simp: lbounds_def split:nat.splits atom.splits)
lemma set_ubounds: "set(ubounds as) = {i. Less 0 (Suc i) \<in> set as}"
by(auto simp: ubounds_def split:nat.splits atom.splits)
lemma set_ebounds:
  "set(ebounds as) = {k. Eq (Suc k) 0 \<in> set as \<or> Eq 0 (Suc k) \<in> set as}"
by(auto simp: ebounds_def split: atom.splits nat.splits)


abbreviation "LB f xs \<equiv> {xs!i|i. Less (Suc i) 0 \<in> set(DLO.atoms\<^sub>0 f)}"
abbreviation "UB f xs \<equiv> {xs!i|i. Less 0 (Suc i) \<in> set(DLO.atoms\<^sub>0 f)}"
definition "EQ f xs = {xs!k|k.
  Eq (Suc k) 0 \<in> set(DLO.atoms\<^sub>0 f) \<or> Eq 0 (Suc k) \<in> set(DLO.atoms\<^sub>0 f)}"


lemma EQ_And[simp]: "EQ (And f g) xs = (EQ f xs \<union> EQ g xs)"
by(auto simp:EQ_def)

lemma EQ_Or[simp]: "EQ (Or f g) xs = (EQ f xs \<union> EQ g xs)"
by(auto simp:EQ_def)

lemma EQ_conv_set_ebounds:
  "x \<in> EQ f xs = (\<exists>e\<in>set(ebounds(DLO.atoms\<^sub>0 f)). x = xs!e)"
by(auto simp: EQ_def set_ebounds)


fun isubst where "isubst k 0 = k" | "isubst k (Suc i) = i"

fun asubst :: "nat \<Rightarrow> atom \<Rightarrow> atom" where
"asubst k (Less i j) = Less (isubst k i) (isubst k j)"|
"asubst k (Eq i j) = Eq (isubst k i) (isubst k j)"

abbreviation "subst \<phi> k \<equiv> map\<^sub>f\<^sub>m (asubst k) \<phi>"

lemma I_subst:
 "qfree f \<Longrightarrow> DLO.I (subst f k) xs = DLO.I f (xs!k # xs)"
apply(induct f)
apply(simp_all)
apply(rename_tac a)
apply(case_tac a)
apply(simp_all add:nth.simps split:nat.splits)
done


fun amin_inf :: "atom \<Rightarrow> atom fm" where
"amin_inf (Less _ 0) = FalseF" |
"amin_inf (Less 0 _) = TrueF" |
"amin_inf (Less (Suc i) (Suc j)) = Atom(Less i j)" |
"amin_inf (Eq 0 0) = TrueF" |
"amin_inf (Eq 0 _) = FalseF" |
"amin_inf (Eq _ 0) = FalseF" |
"amin_inf (Eq (Suc i) (Suc j)) = Atom(Eq i j)"

abbreviation min_inf :: "atom fm \<Rightarrow> atom fm" ("inf\<^sub>-") where
"inf\<^sub>- \<equiv> amap\<^sub>f\<^sub>m amin_inf"

fun aplus_inf :: "atom \<Rightarrow> atom fm" where
"aplus_inf (Less 0 _) = FalseF" |
"aplus_inf (Less _ 0) = TrueF" |
"aplus_inf (Less (Suc i) (Suc j)) = Atom(Less i j)" |
"aplus_inf (Eq 0 0) = TrueF" |
"aplus_inf (Eq 0 _) = FalseF" |
"aplus_inf (Eq _ 0) = FalseF" |
"aplus_inf (Eq (Suc i) (Suc j)) = Atom(Eq i j)"

abbreviation plus_inf :: "atom fm \<Rightarrow> atom fm" ("inf\<^sub>+") where
"inf\<^sub>+ \<equiv> amap\<^sub>f\<^sub>m aplus_inf"

lemma min_inf:
  "nqfree f \<Longrightarrow> \<exists>x. \<forall>y\<le>x. DLO.I (inf\<^sub>- f) xs = DLO.I f (y # xs)"
  (is "_ \<Longrightarrow> \<exists>x. ?P f x")
proof(induct f)
  case (Atom a)
  show ?case
  proof (cases a rule: amin_inf.cases)
    case 1 thus ?thesis by(auto simp add:nth_Cons' linorder_not_less)
  next
    case 2 thus ?thesis
      by (simp) (metis no_lb linorder_not_less order_less_le_trans)
  next
    case 5 thus ?thesis
      by(simp add:nth_Cons') (metis no_lb linorder_not_less)
  next
    case 6 thus ?thesis by simp (metis no_lb linorder_not_less)
  qed simp_all
next
  case (And f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastforce+
  hence "?P (And f1 f2) (min x1 x2)" by(force simp:and_def)
  thus ?case ..
next
  case (Or f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastforce+
  hence "?P (Or f1 f2) (min x1 x2)" by(force simp:or_def)
  thus ?case ..
qed simp_all

lemma plus_inf:
  "nqfree f \<Longrightarrow> \<exists>x.\<forall>y\<ge>x. DLO.I (inf\<^sub>+ f) xs = DLO.I f (y # xs)"
  (is "_ \<Longrightarrow> \<exists>x. ?P f x")
proof (induct f)
  have dlo_bound: "\<And>z::'a. \<exists>x. \<forall>y\<ge>x. y > z"
  proof -
    fix z
    from no_ub obtain w :: 'a where "w > z" ..
    then have "\<forall>y\<ge>w. y > z" by auto
    then show "?thesis z" ..
  qed
  case (Atom a)
  show ?case
  proof (cases a rule: aplus_inf.cases)
    case 1 thus ?thesis
      by (simp add: nth_Cons') (metis linorder_not_less)
  next
    case 2 thus ?thesis by (auto intro: dlo_bound)
  next
    case 5 thus ?thesis 
      by simp (metis dlo_bound less_imp_neq)
  next
    case 6 thus ?thesis
      by simp (metis dlo_bound less_imp_neq)
  qed simp_all
next
  case (And f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastforce+
  hence "?P (And f1 f2) (max x1 x2)" by(force simp:and_def)
  thus ?case ..
next
  case (Or f1 f2)
  then obtain x1 x2 where "?P f1 x1" "?P f2 x2" by fastforce+
  hence "?P (Or f1 f2) (max x1 x2)" by(force simp:or_def)
  thus ?case ..
qed simp_all

context notes [[simp_depth_limit=2]]
begin

lemma LBex:
 "\<lbrakk> nqfree f; DLO.I f (x#xs); \<not>DLO.I (inf\<^sub>- f) xs; x \<notin> EQ f xs \<rbrakk>
  \<Longrightarrow> \<exists>l\<in> LB f xs. l < x"
proof(induct f)
  case (Atom a) thus ?case
    by (cases a rule: amin_inf.cases)
       (simp_all add: nth.simps EQ_def split: nat.splits)
qed auto


lemma UBex:
 "\<lbrakk> nqfree f; DLO.I f (x#xs); \<not>DLO.I (inf\<^sub>+ f) xs; x \<notin> EQ f xs \<rbrakk>
  \<Longrightarrow> \<exists>u \<in> UB f xs. x < u"
proof(induct f)
  case (Atom a) thus ?case
    by (cases a rule: aplus_inf.cases)
       (simp_all add: nth.simps EQ_def split: nat.splits)
qed auto

end

lemma finite_LB: "finite(LB f xs)"
proof -
  have "LB f xs = (\<lambda>k. xs!k) ` set(lbounds(DLO.atoms\<^sub>0 f))"
    by (auto simp:set_lbounds image_def)
  thus ?thesis by simp
qed

lemma finite_UB: "finite(UB f xs)"
proof -
  have "UB f xs = (\<lambda>k.  xs!k) ` set(ubounds(DLO.atoms\<^sub>0 f))"
    by (auto simp:set_ubounds image_def)
  thus ?thesis by simp
qed

lemma qfree_amin_inf: "qfree (amin_inf a)"
by(cases a rule:amin_inf.cases) simp_all

lemma qfree_min_inf: "nqfree \<phi> \<Longrightarrow> qfree(inf\<^sub>- \<phi>)"
by(induct \<phi>)(simp_all add:qfree_amin_inf)

lemma qfree_aplus_inf: "qfree (aplus_inf a)"
by(cases a rule:aplus_inf.cases) simp_all

lemma qfree_plus_inf: "nqfree \<phi> \<Longrightarrow> qfree(inf\<^sub>+ \<phi>)"
by(induct \<phi>)(simp_all add:qfree_aplus_inf)

end
