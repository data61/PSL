section {* The Consensus Data Type *}

theory Consensus
imports RDR
begin

text {* This theory provides a model for the RDR locale, thus showing 
  that the assumption of the RDR locale are consistent. *}

typedecl proc
typedecl val

locale Consensus
-- {* To avoid name clashes *}
begin

fun \<delta>::"val option \<Rightarrow> (proc \<times> val) \<Rightarrow> val option" (infix "\<bullet>" 65) where
  "\<delta> None r = Some (snd r)"
| "\<delta> (Some v) r = Some v"

fun \<gamma>::"val option \<Rightarrow> (proc \<times> val) \<Rightarrow> val" where
  "\<gamma> None r = snd r"
| "\<gamma> (Some v) r = v"

interpretation pre_RDR \<delta> \<gamma> None .
notation exec (infix "\<star>" 65)
notation less_eq (infix "\<preceq>" 50 )
notation None ("\<bottom>")

lemma single_use:
  fixes r rs
  shows  "\<bottom> \<star> ([r]@rs) = Some (snd r)" 
proof (induct rs)
  case Nil
  thus ?case by simp
next
  case (Cons r rs)
  thus ?case by auto
qed

lemma bot: "\<exists> rs . s = \<bottom> \<star> rs"
proof (cases s)
  case None
  hence "s = \<bottom> \<star> []" by auto
  thus ?thesis by blast
next
  case (Some v)
  obtain r where "\<bottom> \<star> [r] = Some v" by force
  thus ?thesis using Some by metis
qed

lemma prec_eq_None_or_equal:
fixes s1 s2
assumes "s1 \<preceq> s2"
shows "s1 = None \<or> s1 = s2" using assms single_use  
proof -
  { assume 1:"s1 \<noteq> None" and 2:"s1 \<noteq> s2"
    obtain r rs where 3:"s1 = \<bottom> \<star> ([r]@rs)" using bot using 1
      by (metis append_butlast_last_id pre_RDR.exec.simps(1)) 
    obtain rs' where 4:"s2 = s1 \<star> rs'" using assms 
      by (auto simp add:less_eq_def)
    have "s2 = \<bottom> \<star> ([r]@(rs@rs'))" using 3 4
      by (metis exec_append) 
    hence "s1 = s2" using 3
      by (metis single_use)
    with 2 have False by auto }
  thus ?thesis by blast
qed

interpretation RDR \<delta> \<gamma> \<bottom>
proof (unfold_locales)
  fix s r 
  assume "contains s r"
  show "s \<bullet> r = s"
  proof -
    obtain rs where "s = \<bottom> \<star> rs" and "rs \<noteq> []" 
      using `contains s r`
      by (auto simp add:contains_def, force)
    thus ?thesis
    by (metis \<delta>.simps(2) rev_exhaust single_use)
  qed
next
  fix s and r r' :: "proc \<times> val"
  assume 1:"fst r \<noteq> fst r'"
  thus "\<gamma> s r = \<gamma> ((s \<bullet> r) \<bullet> r') r"
    by (metis \<delta>.simps \<gamma>.simps not_Some_eq)
next
  fix s1 s2
  assume "s1 \<preceq> s2 \<and> s2 \<preceq> s1"
  thus "s1 = s2" by (metis prec_eq_None_or_equal) 
next
  fix s1 s2
  show "\<exists> s . is_glb s s1 s2" 
  by (simp add:is_glb_def is_lb_def)
    (metis bot pre_RDR.less_eq_def prec_eq_None_or_equal) 
next
  fix s
  show "\<bottom> \<preceq> s"
  by (metis bot pre_RDR.less_eq_def)
next
  fix s1 s2 s3 rs
  assume "s1 \<preceq> s2" and "s2 \<preceq> s3" and "s3 = s1 \<star> rs"
  thus "\<exists> rs' rs'' . s2 = s1 \<star> rs' \<and> s3 = s2 \<star> rs'' 
    \<and> set rs' \<subseteq> set rs \<and> set rs'' \<subseteq> set rs"
  by (metis Consensus.prec_eq_None_or_equal 
      in_set_insert insert_Nil list.distinct(1)
        pre_RDR.exec.simps(1) subsetI)
qed

end

end
