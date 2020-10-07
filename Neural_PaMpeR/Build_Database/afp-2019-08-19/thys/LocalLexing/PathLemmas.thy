theory PathLemmas
imports TheoremD14
begin

context LocalLexing begin

lemma characterize_\<P>:
  "(\<forall> i < length p. \<exists>u. p ! i \<in> \<Z> (charslength (take i p)) u) \<Longrightarrow> admissible p \<Longrightarrow>
  \<exists> u. p \<in> \<P> (charslength p) u"
proof (induct p rule: rev_induct)
  case Nil
    show ?case by simp
next
  case (snoc a p)
    from snoc.prems have admissible_p: "admissible p"
      by (metis append_Nil2 is_prefix_admissible is_prefix_cancel is_prefix_empty) 
    {
      fix i :: nat
      assume ilen: "i < length p"
      then have "i < length (p@[a])"
        by (simp add: Suc_leI Suc_le_lessD trans_le_add1) 
      with snoc have "\<exists>u. (p @ [a]) ! i \<in> \<Z> (charslength (take i (p @ [a]))) u"
        by blast
      then obtain u where u: "(p @ [a]) ! i \<in> \<Z> (charslength (take i (p @ [a]))) u" by blast
      from ilen have p_at: "(p @ [a]) ! i = p ! i" by (simp add: nth_append)  
      from ilen have p_take: "take i (p @ [a]) = take i p" by (simp add: less_or_eq_imp_le) 
      from u p_at p_take have p_i: "p ! i \<in> \<Z> (charslength (take i p)) u" by simp 
      then have "\<exists> u. p ! i \<in> \<Z> (charslength (take i p)) u" by blast
    }
    then have "\<forall> i < length p. \<exists>u. p ! i \<in> \<Z> (charslength (take i p)) u" by auto
    with admissible_p snoc.hyps obtain u where u: "p \<in> \<P> (charslength p) u" by blast
    have "\<exists>u. (p @ [a]) ! (length p) \<in> \<Z> (charslength (take (length p) (p @ [a]))) u"
      using snoc
      by (metis (no_types, hide_lams) add_Suc_right append_Nil2 length_Cons length_append 
        less_Suc_eq_le less_or_eq_imp_le) 
    then obtain v where "(p @ [a]) ! (length p) \<in> \<Z> (charslength (take (length p) (p @ [a]))) v"
      by blast
    then have v: "a \<in> \<Z> (charslength p) v" by simp
    {
      assume v_leq_u: "v \<le> u"
      then have "a \<in> \<Z> (charslength p) (Suc u)" using v
        by (meson LocalLexing.subset_fSuc LocalLexing_axioms \<Z>_subset_Suc subsetCE) 
      from path_append_token[OF u this snoc.prems(2)] 
      have "p @ [a] \<in> \<P> (charslength p) (Suc u)" by blast
      then have ?case using in_\<P>_charslength by blast 
    }
    note case_v_leq_u = this
    {
      assume u_less_v: "u < v"
      then obtain w where w: "v = Suc w" using less_imp_Suc_add by blast 
      with u_less_v have "u \<le> w" by arith
      with u have "p \<in> \<P> (charslength p) w" by (meson subsetCE subset_\<P>k) 
      from v w path_append_token[OF this _ snoc.prems(2)] 
      have "p @ [a] \<in> \<P> (charslength p) (Suc w)" by blast
      then have ?case using in_\<P>_charslength by blast 
    }
    note case_u_less_v = this
    
    show ?case using case_v_leq_u case_u_less_v not_le by blast 
qed

lemma drop_empty_tokens: 
  assumes p: "p \<in> \<PP>"
  assumes r: "r \<le> length p"
  assumes empty: "charslength (take r p) = 0"
  assumes admissible: "admissible (drop r p)"
  shows "drop r p \<in> \<PP>"
proof -
  have p_\<Z>: "\<forall>i<length p. \<exists>u. p ! i \<in> \<Z> (charslength (take i p)) u" using p
    using tokens_nth_in_\<Z> by blast 
  obtain q where q: "q = drop r p" by blast
  {
    fix j :: nat
    assume j : "j < length q"
    have length_p_q_r: "length p = length q + r"
      using r q add.commute diff_add_inverse le_Suc_ex length_drop by simp
    have j_plus_r_bound: "j + r < length p" by (simp add: j length_p_q_r) 
    with p_\<Z> have "\<exists>u. p ! (j + r) \<in> \<Z> (charslength (take (j + r) p)) u" by blast
    then obtain u where u: "p ! (j + r) \<in> \<Z> (charslength (take (j + r) p)) u" by blast
    have p_at_is_q_at: "p ! (j + r) = q ! j" by (simp add: add.commute q r) 
    have "take (j + r) p = (take r p) @ (take j q)" by (metis add.commute q take_add)
    with empty have "charslength (take (j + r) p) = charslength (take j q)" by auto
    with u p_at_is_q_at have "q ! j \<in> \<Z> (charslength (take j q)) u" by simp
    then have "\<exists> u. q ! j \<in> \<Z> (charslength (take j q)) u" by auto
  }
  then have "\<forall>i<length q. \<exists>u. q ! i \<in> \<Z> (charslength (take i q)) u" by blast
  from characterize_\<P>[OF this] have "\<exists>u. q \<in> \<P> (charslength q) u" using admissible q by auto
  then show ?thesis using \<PP>_covers_\<P> q by blast 
qed
  
end

end
