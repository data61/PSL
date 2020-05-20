theory General_Utils
  imports "HOL-Analysis.Analysis"
begin

lemma lambda_skolem_gen: "(\<forall>i. \<exists>f'::('a ^ 'n) \<Rightarrow> 'a. P i f') \<longleftrightarrow>
   (\<exists>f'::('a ^ 'n) \<Rightarrow> ('a ^ 'n). \<forall>i. P i ((\<lambda>x. (f' x) $ i)))" (is "?lhs \<longleftrightarrow> ?rhs")
  (*using choice_iff lambda_skolem*)
proof -
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f'' where f'':"\<forall>i. P i (f'' i)" unfolding choice_iff
      by metis
    let ?x = "(\<lambda>x. (\<chi> i. (f''  i) x))"
    { fix i
      from f'' have "P i (f'' i)" by metis
      then have "P i (\<lambda>x.(?x x) $ i)" by auto
    }
    hence "\<forall>i. P i (\<lambda>x.(?x x) $ i)" by metis
    hence ?rhs by metis}
  ultimately show ?thesis by metis
qed

lemma lambda_skolem_euclidean: "(\<forall>i\<in>Basis. \<exists>f'::('a::{euclidean_space}\<Rightarrow>real). P i f') \<longleftrightarrow>
   (\<exists>f'::('a::euclidean_space\<Rightarrow>'b::euclidean_space). \<forall>i\<in>Basis. P i ((\<lambda>x. (f' x) \<bullet> i)))" (is "?lhs \<longleftrightarrow> ?rhs")
  (*using choice_iff lambda_skolem*)
proof -
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f'' where f'':"\<forall>i::('b::euclidean_space)\<in>Basis. P i (f'' i)" unfolding choice_iff
      by metis
    let ?x = "(\<lambda>x. (\<Sum>i\<in>Basis. ((f''  i) x) *\<^sub>R i))"
    { fix i::"'b::euclidean_space"
      assume ass: "i\<in>Basis"
      then have "P i (f'' i)"
        using f''
        by metis
      then have "P i (\<lambda>x.(?x x) \<bullet> i)" using ass by auto
    }
    hence *: "\<forall>i\<in>Basis. P i (\<lambda>x.(?x x) \<bullet> i)" by auto
    then have ?rhs
      apply auto
    proof
      let ?f'6 = ?x
      show " \<forall>i\<in>Basis. P i (\<lambda>x. ?f'6 x \<bullet> i)" using * by auto
    qed}
  ultimately show ?thesis by metis
qed

lemma lambda_skolem_euclidean_explicit: "(\<forall>i\<in>Basis. \<exists>f'::('a::{euclidean_space}\<Rightarrow>real). P i f') \<longleftrightarrow>
   (\<exists>f'::('a::{euclidean_space}\<Rightarrow>'a). \<forall>i\<in>Basis. P i ((\<lambda>x. (f' x) \<bullet> i)))" (is "?lhs \<longleftrightarrow> ?rhs")
  (*using choice_iff lambda_skolem*)
proof -
  { assume H: "?rhs"
    then have ?lhs by auto }
  moreover
  { assume H: "?lhs"
    then obtain f'' where f'':"\<forall>i::('a::euclidean_space)\<in>Basis. P i (f'' i)" unfolding choice_iff
      by metis
    let ?x = "(\<lambda>x. (\<Sum>i\<in>Basis. ((f''  i) x) *\<^sub>R i))"
    { fix i::"'a::euclidean_space"
      assume ass: "i\<in>Basis"
      then have "P i (f'' i)"
        using f''
        by metis
      then have "P i (\<lambda>x.(?x x) \<bullet> i)" using ass by auto
    }
    hence *: "\<forall>i\<in>Basis. P i (\<lambda>x.(?x x) \<bullet> i)" by auto
    then have ?rhs
      apply auto
    proof
      let ?f'6 = ?x
      show " \<forall>i\<in>Basis. P i (\<lambda>x. ?f'6 x \<bullet> i)" using * by auto
    qed}
  ultimately show ?thesis by metis
qed

lemma indic_ident:
  "\<And> (f::'a \<Rightarrow> real) s. (\<lambda>x. (f x) * indicator s x) = (\<lambda>x. if x \<in> s then f x else 0)"
proof
  fix f::"'a \<Rightarrow> real"
  fix s::"'a set"
  fix x:: 'a
  show " f x * indicator s x = (if x \<in> s then f x else 0)"
    by (simp add: indicator_def)
qed

lemma real_pair_basis: "Basis = {(1::real,0::real), (0::real,1::real)}"
  by (simp add: Basis_prod_def insert_commute)


(*AE_measure_singleton*)

lemma real_singleton_in_borel:
  shows "{a::real} \<in> sets borel"
  using Borel_Space.cbox_borel[of "a" "a"]
  apply auto
  done

lemma real_singleton_in_lborel:
  shows "{a::real} \<in> sets lborel"
  using real_singleton_in_borel
  apply auto
  done

lemma cbox_diff:
  shows "{0::real..1} - {0,1} = box 0 1"
  by (auto simp add: cbox_def)

lemma sum_bij:
  assumes "bij F"
    "\<forall>x\<in>s. f x = g (F x)"
  shows "\<And>t. F ` s =  t \<Longrightarrow> sum f s = sum g t"
  by (metis assms bij_betw_def bij_betw_subset subset_UNIV sum.reindex_cong)

abbreviation surj_on where
  "surj_on s f \<equiv> s \<subseteq> range f"

lemma surj_on_image_vimage_eq: "surj_on s f \<Longrightarrow> f ` (f -` s) = s"
  by fastforce

end
