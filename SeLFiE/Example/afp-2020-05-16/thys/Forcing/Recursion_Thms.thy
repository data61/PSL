section\<open>Some enhanced theorems on recursion\<close>

theory Recursion_Thms imports ZF.Epsilon begin

text\<open>We prove results concerning definitions by well-founded
recursion on some relation \<^term>\<open>R\<close> and its transitive closure
\<^term>\<open>R^*\<close>\<close>
  (* Restrict the relation r to the field A*A *)

lemma fld_restrict_eq : "a \<in> A \<Longrightarrow> (r \<inter> A\<times>A)-``{a} = (r-``{a} \<inter> A)"
  by(force)

lemma fld_restrict_mono : "relation(r) \<Longrightarrow> A \<subseteq> B \<Longrightarrow> r \<inter> A\<times>A \<subseteq> r \<inter> B\<times>B"
  by(auto)

lemma fld_restrict_dom :
  assumes "relation(r)" "domain(r) \<subseteq> A" "range(r)\<subseteq> A"
  shows "r\<inter> A\<times>A = r"
proof (rule equalityI,blast,rule subsetI)
  { fix x
    assume xr: "x \<in> r"
    from xr assms have "\<exists> a b . x = \<langle>a,b\<rangle>" by (simp add: relation_def)
    then obtain a b where "\<langle>a,b\<rangle> \<in> r" "\<langle>a,b\<rangle> \<in> r\<inter>A\<times>A" "x \<in> r\<inter>A\<times>A"
      using assms xr
      by force
    then have "x\<in> r \<inter> A\<times>A" by simp
  }
  then show "x \<in> r \<Longrightarrow> x\<in> r\<inter>A\<times>A" for x .
qed

definition tr_down :: "[i,i] \<Rightarrow> i"
  where "tr_down(r,a) = (r^+)-``{a}"

lemma tr_downD : "x \<in> tr_down(r,a) \<Longrightarrow> \<langle>x,a\<rangle> \<in> r^+"
  by (simp add: tr_down_def vimage_singleton_iff)

lemma pred_down : "relation(r) \<Longrightarrow> r-``{a} \<subseteq> tr_down(r,a)"
  by(simp add: tr_down_def vimage_mono r_subset_trancl)

lemma tr_down_mono : "relation(r) \<Longrightarrow> x \<in> r-``{a} \<Longrightarrow> tr_down(r,x) \<subseteq> tr_down(r,a)"
  by(rule subsetI,simp add:tr_down_def,auto dest: underD,force simp add: underI r_into_trancl trancl_trans)

lemma rest_eq :
  assumes "relation(r)" and "r-``{a} \<subseteq> B" and "a \<in> B"
  shows "r-``{a} = (r\<inter>B\<times>B)-``{a}"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> r-``{a}"
  then
  have "x \<in> B" using assms by (simp add: subsetD)
  from \<open>x\<in> r-``{a}\<close>
  have "\<langle>x,a\<rangle> \<in> r" using underD by simp
  then
  show "x \<in> (r\<inter>B\<times>B)-``{a}" using \<open>x\<in>B\<close> \<open>a\<in>B\<close> underI by simp
next
  from assms
  show "x \<in> r -`` {a}" if  "x \<in> (r \<inter> B\<times>B) -`` {a}" for x
    using vimage_mono that by auto
qed

lemma wfrec_restr_eq : "r' = r \<inter> A\<times>A \<Longrightarrow> wfrec[A](r,a,H) = wfrec(r',a,H)"
  by(simp add:wfrec_on_def)

lemma wfrec_restr :
  assumes rr: "relation(r)" and wfr:"wf(r)"
  shows  "a \<in> A \<Longrightarrow> tr_down(r,a) \<subseteq> A \<Longrightarrow> wfrec(r,a,H) = wfrec[A](r,a,H)"
proof (induct a arbitrary:A rule:wf_induct_raw[OF wfr] )
  case (1 a)
  have wfRa : "wf[A](r)"
    using wf_subset wfr wf_on_def Int_lower1 by simp
  from pred_down rr
  have "r -`` {a} \<subseteq> tr_down(r, a)" .
  with 1
  have "r-``{a} \<subseteq> A" by (force simp add: subset_trans)
  {
    fix x
    assume x_a : "x \<in> r-``{a}"
    with \<open>r-``{a} \<subseteq> A\<close>
    have "x \<in> A" ..
    from pred_down rr
    have b : "r -``{x} \<subseteq> tr_down(r,x)" .
    then
    have "tr_down(r,x) \<subseteq> tr_down(r,a)"
      using tr_down_mono x_a rr by simp
    with 1
    have "tr_down(r,x) \<subseteq> A" using subset_trans by force
    have "\<langle>x,a\<rangle> \<in> r" using x_a  underD by simp
    with 1 \<open>tr_down(r,x) \<subseteq> A\<close> \<open>x \<in> A\<close>
    have "wfrec(r,x,H) = wfrec[A](r,x,H)" by simp
  }
  then
  have "x\<in> r-``{a} \<Longrightarrow> wfrec(r,x,H) =  wfrec[A](r,x,H)" for x  .
  then
  have Eq1 :"(\<lambda> x \<in> r-``{a} . wfrec(r,x,H)) = (\<lambda> x \<in> r-``{a} . wfrec[A](r,x,H))"
    using lam_cong by simp

  from assms
  have "wfrec(r,a,H) = H(a,\<lambda> x \<in> r-``{a} . wfrec(r,x,H))" by (simp add:wfrec)
  also
  have "... = H(a,\<lambda> x \<in> r-``{a} . wfrec[A](r,x,H))"
    using assms Eq1 by simp
  also from 1 \<open>r-``{a} \<subseteq> A\<close>
  have "... = H(a,\<lambda> x \<in> (r\<inter>A\<times>A)-``{a} . wfrec[A](r,x,H))"
    using assms rest_eq  by simp
  also from \<open>a\<in>A\<close>
  have "... = H(a,\<lambda> x \<in> (r-``{a})\<inter>A . wfrec[A](r,x,H))"
    using fld_restrict_eq by simp
  also from \<open>a\<in>A\<close> \<open>wf[A](r)\<close>
  have "... = wfrec[A](r,a,H)" using wfrec_on by simp
  finally show ?case .
qed

lemmas wfrec_tr_down = wfrec_restr[OF _ _ _ subset_refl]

lemma wfrec_trans_restr : "relation(r) \<Longrightarrow> wf(r) \<Longrightarrow> trans(r) \<Longrightarrow> r-``{a}\<subseteq>A \<Longrightarrow> a \<in> A \<Longrightarrow>
  wfrec(r, a, H) = wfrec[A](r, a, H)"
  by(subgoal_tac "tr_down(r,a) \<subseteq> A",auto simp add : wfrec_restr tr_down_def trancl_eq_r)


lemma field_trancl : "field(r^+) = field(r)"
  by (blast intro: r_into_trancl dest!: trancl_type [THEN subsetD])

definition
  Rrel :: "[i\<Rightarrow>i\<Rightarrow>o,i] \<Rightarrow> i" where
  "Rrel(R,A) \<equiv> {z\<in>A\<times>A. \<exists>x y. z = \<langle>x, y\<rangle> \<and> R(x,y)}"

lemma RrelI : "x \<in> A \<Longrightarrow> y \<in> A \<Longrightarrow> R(x,y) \<Longrightarrow> \<langle>x,y\<rangle> \<in> Rrel(R,A)"
  unfolding Rrel_def by simp

lemma Rrel_mem: "Rrel(mem,x) = Memrel(x)"
  unfolding Rrel_def Memrel_def ..

lemma relation_Rrel: "relation(Rrel(R,d))"
  unfolding Rrel_def relation_def by simp

lemma field_Rrel: "field(Rrel(R,d)) \<subseteq>  d"
  unfolding Rrel_def by auto

lemma Rrel_mono : "A \<subseteq> B \<Longrightarrow> Rrel(R,A) \<subseteq> Rrel(R,B)"
  unfolding Rrel_def by blast

lemma Rrel_restr_eq : "Rrel(R,A) \<inter> B\<times>B = Rrel(R,A\<inter>B)"
  unfolding Rrel_def by blast

(* now a consequence of the previous lemmas *)
lemma field_Memrel : "field(Memrel(A)) \<subseteq> A"
  (* unfolding field_def using Ordinal.Memrel_type by blast *)
  using Rrel_mem field_Rrel by blast

lemma restrict_trancl_Rrel:
  assumes "R(w,y)"
  shows "restrict(f,Rrel(R,d)-``{y})`w
       = restrict(f,(Rrel(R,d)^+)-``{y})`w"
proof (cases "y\<in>d")
  let ?r="Rrel(R,d)" and ?s="(Rrel(R,d))^+"
  case True
  show ?thesis
  proof (cases "w\<in>d")
    case True
    with \<open>y\<in>d\<close> assms
    have "\<langle>w,y\<rangle>\<in>?r"
      unfolding Rrel_def by blast
    then
    have "\<langle>w,y\<rangle>\<in>?s"
      using r_subset_trancl[of ?r] relation_Rrel[of R d] by blast
    with \<open>\<langle>w,y\<rangle>\<in>?r\<close>
    have "w\<in>?r-``{y}" "w\<in>?s-``{y}"
      using vimage_singleton_iff by simp_all
    then
    show ?thesis by simp
  next
    case False
    then
    have "w\<notin>domain(restrict(f,?r-``{y}))"
      using subsetD[OF field_Rrel[of R d]] by auto
    moreover from \<open>w\<notin>d\<close>
    have "w\<notin>domain(restrict(f,?s-``{y}))"
      using subsetD[OF field_Rrel[of R d], of w] field_trancl[of ?r]
        fieldI1[of w y ?s] by auto
    ultimately
    have "restrict(f,?r-``{y})`w = 0" "restrict(f,?s-``{y})`w = 0"
      unfolding apply_def by auto
    then show ?thesis by simp
  qed
next
  let ?r="Rrel(R,d)"
  let ?s="?r^+"
  case False
  then
  have "?r-``{y}=0"
    unfolding Rrel_def by blast
  then
  have "w\<notin>?r-``{y}" by simp
  with \<open>y\<notin>d\<close> assms
  have "y\<notin>field(?s)"
    using field_trancl subsetD[OF field_Rrel[of R d]] by force
  then
  have "w\<notin>?s-``{y}"
    using vimage_singleton_iff by blast
  with \<open>w\<notin>?r-``{y}\<close>
  show ?thesis by simp
qed

lemma restrict_trans_eq:
  assumes "w \<in> y"
  shows "restrict(f,Memrel(eclose({x}))-``{y})`w
       = restrict(f,(Memrel(eclose({x}))^+)-``{y})`w"
  using assms restrict_trancl_Rrel[of mem ] Rrel_mem by (simp)

lemma wf_eq_trancl:
  assumes "\<And> f y . H(y,restrict(f,R-``{y})) = H(y,restrict(f,R^+-``{y}))"
  shows  "wfrec(R, x, H) = wfrec(R^+, x, H)" (is "wfrec(?r,_,_) = wfrec(?r',_,_)")
proof -
  have "wfrec(R, x, H) = wftrec(?r^+, x, \<lambda>y f. H(y, restrict(f,?r-``{y})))"
    unfolding wfrec_def ..
  also
  have " ... = wftrec(?r^+, x, \<lambda>y f. H(y, restrict(f,(?r^+)-``{y})))"
    using assms by simp
  also
  have " ... =  wfrec(?r^+, x, H)"
    unfolding wfrec_def using trancl_eq_r[OF relation_trancl trans_trancl] by simp
  finally
  show ?thesis .
qed

end
