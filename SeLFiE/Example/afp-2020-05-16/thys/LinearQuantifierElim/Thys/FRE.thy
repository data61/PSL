(*  Author:     Tobias Nipkow, 2007  *)

theory FRE
imports LinArith
begin

subsection\<open>Ferrante-Rackoff \label{sec:FRE}\<close>

text\<open>This section formalizes a slight variant of Ferrante and
Rackoff's algorithm~\cite{FerranteR-SIAM75}. We consider equalities
separately, which improves performance.\<close>

fun between :: "real * real list \<Rightarrow> real * real list \<Rightarrow> real * real list"
where "between (r,cs) (s,ds) = ((r+s)/2, (1/2) *\<^sub>s (cs+ds))"

definition FR\<^sub>1 :: "atom fm \<Rightarrow> atom fm" where
"FR\<^sub>1 \<phi> =
(let as = R.atoms\<^sub>0 \<phi>; lbs = lbounds as; ubs = ubounds as; ebs = ebounds as;
     intrs = [subst \<phi> (between l u) . l \<leftarrow> lbs, u \<leftarrow> ubs]
 in list_disj (inf\<^sub>- \<phi> # inf\<^sub>+ \<phi> # intrs @ map (subst \<phi>) ebs))"


lemma dense_interval:
assumes "finite L" "finite U" "l \<in> L" "u \<in> U" "l < x" "x < u" "P(x::real)"
and dense: "\<And>y l u. \<lbrakk> \<forall>y\<in>{l<..<x}. y \<notin> L;  \<forall>y\<in>{x<..<u}. y \<notin> U;
                       l<x;x<u; l<y;y<u \<rbrakk> \<Longrightarrow> P y"
shows "\<exists>l\<in>L.\<exists>u\<in>U. l<u \<and> (\<forall>y. l<y \<and> y<u \<longrightarrow> P y)"
proof -
  let ?L = "{l:L. l < x}" let ?U = "{u:U. x < u}"
  let ?ll = "Max ?L" let ?uu = "Min ?U"
  have "?L \<noteq> {}" using \<open>l \<in> L\<close> \<open>l<x\<close> by (blast intro:order_less_imp_le)
  moreover have "?U \<noteq> {}" using \<open>u:U\<close> \<open>x<u\<close> by (blast intro:order_less_imp_le)
  ultimately have "\<forall>y. ?ll<y \<and> y<x \<longrightarrow> y \<notin> L" "\<forall>y. x<y \<and> y<?uu \<longrightarrow> y \<notin> U"
    using \<open>finite L\<close> \<open>finite U\<close> by force+
  moreover have "?ll \<in> L"
  proof
    show "?ll \<in> ?L" using \<open>finite L\<close> Max_in[OF _ \<open>?L \<noteq> {}\<close>] by simp
    show "?L \<subseteq> L" by blast
  qed
  moreover have "?uu \<in> U"
  proof
    show "?uu \<in> ?U" using \<open>finite U\<close> Min_in[OF _ \<open>?U \<noteq> {}\<close>] by simp
    show "?U \<subseteq> U" by blast
  qed
  moreover have "?ll < x" using \<open>finite L\<close> \<open>?L \<noteq> {}\<close> by simp
  moreover have "x < ?uu" using \<open>finite U\<close> \<open>?U \<noteq> {}\<close> by simp
  moreover have "?ll < ?uu" using \<open>?ll<x\<close> \<open>x<?uu\<close> by arith
  ultimately show ?thesis using \<open>l < x\<close> \<open>x < u\<close> \<open>?L \<noteq> {}\<close> \<open>?U \<noteq> {}\<close>
    by(blast intro!:dense greaterThanLessThan_iff[THEN iffD1])
qed

lemma dense:
  "\<lbrakk> nqfree f; \<forall>y\<in>{l<..<x}. y \<notin> LB f xs; \<forall>y\<in>{x<..<u}. y \<notin> UB f xs;
     l < x; x < u; x \<notin> EQ f xs;  R.I f (x#xs); l < y; y < u\<rbrakk>
   \<Longrightarrow> R.I f (y#xs)"
proof(induct f)
  case (Atom a)
  show ?case
  proof (cases a)
    case (Less r cs)
    show ?thesis
    proof (cases cs)
      case Nil thus ?thesis using Atom Less by (simp add:depends\<^sub>R_def)
    next
      case (Cons c cs)
      hence "r < c*x + \<langle>cs,xs\<rangle>" using Atom Less by simp
      { assume "c=0" hence ?thesis using Atom Less Cons by simp }
      moreover
      { assume "c<0"
        hence "x < (r - \<langle>cs,xs\<rangle>)/c" (is "_ < ?u") using \<open>r < c*x + \<langle>cs,xs\<rangle>\<close>
          by (simp add: field_simps)
        have ?thesis
        proof (rule ccontr)
          assume "\<not> R.I (Atom a) (y#xs)"
          hence "?u \<le> y" using Atom Less Cons \<open>c<0\<close>
            by (auto simp add: field_simps)
          hence "?u < u" using \<open>y<u\<close> by simp
          with \<open>x<?u\<close> show False using Atom Less Cons \<open>c<0\<close>
            by(auto simp:depends\<^sub>R_def)
        qed } moreover
      { assume "c>0"
        hence "x > (r - \<langle>cs,xs\<rangle>)/c" (is "_ > ?l") using \<open>r < c*x + \<langle>cs,xs\<rangle>\<close>
          by (simp add: field_simps)
        have ?thesis
        proof (rule ccontr)
          assume "\<not> R.I (Atom a) (y#xs)"
          hence "?l \<ge> y" using Atom Less Cons \<open>c>0\<close>
            by (auto simp add: field_simps)
          hence "?l > l" using \<open>y>l\<close> by simp
          with \<open>?l<x\<close> show False using Atom Less Cons \<open>c>0\<close>
            by (auto simp:depends\<^sub>R_def)
        qed }
      ultimately show ?thesis by force
    qed
  next
    case (Eq r cs)
    show ?thesis
    proof (cases cs)
      case Nil thus ?thesis using Atom Eq by (simp add:depends\<^sub>R_def)
    next
      case (Cons c cs)
      hence "r = c*x + \<langle>cs,xs\<rangle>" using Atom Eq by simp
      { assume "c=0" hence ?thesis using Atom Eq Cons by simp }
      moreover
      { assume "c\<noteq>0"
        hence ?thesis using \<open>r = c*x + \<langle>cs,xs\<rangle>\<close> Atom Eq Cons \<open>l<y\<close> \<open>y<u\<close>
          by(auto simp: ac_simps depends\<^sub>R_def split:if_splits) }
      ultimately show ?thesis by force
    qed
  qed
next
  case (And f1 f2) thus ?case
    by auto (metis (no_types, hide_lams))+
next
  case (Or f1 f2) thus ?case
    by auto (metis (no_types, hide_lams))+
qed fastforce+

theorem I_FR\<^sub>1:
assumes "nqfree \<phi>" shows "R.I (FR\<^sub>1 \<phi>) xs = (\<exists>x. R.I \<phi> (x#xs))"
  (is "?FR = ?EX")
proof
  assume ?FR
  { assume "R.I (inf\<^sub>- \<phi>) xs"
    hence ?EX using \<open>?FR\<close> min_inf[OF \<open>nqfree \<phi>\<close>, where xs=xs]
      by(auto simp add:FR\<^sub>1_def)
  } moreover
  { assume "R.I (inf\<^sub>+ \<phi>) xs"
    hence ?EX using \<open>?FR\<close> plus_inf[OF \<open>nqfree \<phi>\<close>, where xs=xs]
      by(auto simp add:FR\<^sub>1_def)
  } moreover
  { assume "\<exists>x \<in> EQ \<phi> xs. R.I \<phi> (x#xs)"
    hence ?EX using \<open>?FR\<close> by(auto simp add:FR\<^sub>1_def)
  } moreover
  { assume "\<not>R.I (inf\<^sub>- \<phi>) xs \<and> \<not>R.I (inf\<^sub>+ \<phi>) xs \<and>
            (\<forall>x\<in>EQ \<phi> xs. \<not>R.I \<phi> (x#xs))"
    with \<open>?FR\<close> obtain r cs s ds
      where "R.I (subst \<phi> (between (r,cs) (s,ds))) xs"
      by(auto simp: FR\<^sub>1_def eval_def
        diff_divide_distrib set_ebounds I_subst \<open>nqfree \<phi>\<close>) blast
    hence "R.I \<phi> (eval (between (r,cs) (s,ds)) xs # xs)"
      by(simp add:I_subst \<open>nqfree \<phi>\<close>)
    hence ?EX .. }
  ultimately show ?EX by blast
next
  assume ?EX
  then obtain x where x: "R.I \<phi> (x#xs)" ..
  { assume "R.I (inf\<^sub>- \<phi>) xs \<or> R.I (inf\<^sub>+ \<phi>) xs"
    hence ?FR by(auto simp:FR\<^sub>1_def)
  } moreover
  { assume "x \<in> EQ \<phi> xs"
    then obtain r cs
      where "(r,cs) \<in> set(ebounds(R.atoms\<^sub>0 \<phi>)) \<and> x = r + \<langle>cs,xs\<rangle>"
      by(force simp:set_ebounds field_simps)
    moreover hence "R.I (subst \<phi> (r,cs)) xs" using x
      by(auto simp: I_subst \<open>nqfree \<phi>\<close> eval_def)
    ultimately have ?FR by(force simp:FR\<^sub>1_def) } moreover
  { assume "\<not> R.I (inf\<^sub>- \<phi>) xs" and "\<not> R.I (inf\<^sub>+ \<phi>) xs" and "x \<notin> EQ \<phi> xs"
    obtain l where "l \<in> LB \<phi> xs" "l < x"
      using LBex[OF \<open>nqfree \<phi>\<close> x \<open>\<not> R.I (inf\<^sub>- \<phi>) xs\<close> \<open>x \<notin> EQ \<phi> xs\<close>] ..
    obtain u where "u \<in> UB \<phi> xs" "x < u"
      using UBex[OF \<open>nqfree \<phi>\<close> x \<open>\<not> R.I (inf\<^sub>+ \<phi>) xs\<close> \<open>x \<notin> EQ \<phi> xs\<close>] ..
    have "\<exists>l\<in>LB \<phi> xs. \<exists>u\<in>UB \<phi> xs. l<u \<and> (\<forall>y. l < y \<and> y < u \<longrightarrow> R.I \<phi> (y#xs))"
      using dense_interval[where P = "\<lambda>x. R.I \<phi> (x#xs)", OF finite_LB finite_UB \<open>l:LB \<phi> xs\<close> \<open>u:UB \<phi> xs\<close> \<open>l<x\<close> \<open>x<u\<close> x] x dense[OF \<open>nqfree \<phi>\<close> _ _ _ _ \<open>x \<notin> EQ \<phi> xs\<close>] by simp
    then obtain r c cs s d ds
      where "Less r (c # cs) \<in> set (R.atoms\<^sub>0 \<phi>)" "Less s (d # ds) \<in> set (R.atoms\<^sub>0 \<phi>)"
          "\<And>y. (r - \<langle>cs,xs\<rangle>) / c < y \<Longrightarrow> y < (s - \<langle>ds,xs\<rangle>) / d \<Longrightarrow> R.I \<phi> (y # xs)"
        and *: "c > 0" "d < 0" "(r - \<langle>cs,xs\<rangle>) / c < (s - \<langle>ds,xs\<rangle>) / d"
      by blast
    moreover
      have "(r - \<langle>cs,xs\<rangle>) / c < eval (between (r / c, (-1 / c) *\<^sub>s cs) (s / d, (-1 / d) *\<^sub>s ds)) xs" (is ?P)
        and "eval (between (r / c, (-1 / c) *\<^sub>s cs) (s / d, (-1 / d) *\<^sub>s ds)) xs < (s - \<langle>ds,xs\<rangle>) / d" (is ?Q)
    proof -
      from * have [simp]: "c * (c * (d * (d * 4))) > 0"
        by (simp add: algebra_split_simps)
      from * have "c * s + d * \<langle>cs,xs\<rangle> < d * r + c * \<langle>ds,xs\<rangle>"
        by (simp add: field_simps)
      with * have "(2 * c * c * d) * (d * r + c * \<langle>ds,xs\<rangle>)
        < (2 * c * c * d) * (c * s + d * \<langle>cs,xs\<rangle>)"
        and "(2 * c * d * d) * (c * s + d * \<langle>cs,xs\<rangle>)
        < (2 * c * d * d) * (d * r + c * \<langle>ds,xs\<rangle>)" by simp_all
      with * show ?P and ?Q by (auto simp add: field_simps eval_def iprod_left_add_distrib)
    qed
    ultimately have ?FR
      by (fastforce simp: FR\<^sub>1_def bex_Un set_lbounds set_ubounds set_ebounds I_subst \<open>nqfree \<phi>\<close>)
  } ultimately show ?FR by blast
qed


definition "FR = R.lift_nnf_qe FR\<^sub>1"


lemma qfree_FR\<^sub>1: "nqfree \<phi> \<Longrightarrow> qfree (FR\<^sub>1 \<phi>)"
apply(simp add:FR\<^sub>1_def)
apply(rule qfree_list_disj)
apply(auto simp:qfree_min_inf qfree_plus_inf set_ubounds set_lbounds set_ebounds image_def qfree_map_fm)
done

theorem I_FR: "R.I (FR \<phi>) xs = R.I \<phi> xs"
by(simp add:I_FR\<^sub>1 FR_def R.I_lift_nnf_qe qfree_FR\<^sub>1)

theorem qfree_FR: "qfree (FR \<phi>)"
by(simp add:FR_def R.qfree_lift_nnf_qe qfree_FR\<^sub>1)

end
