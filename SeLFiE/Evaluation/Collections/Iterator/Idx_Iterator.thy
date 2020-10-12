section \<open>\isaheader{Iterator by get and size }\<close>
theory Idx_Iterator
imports
  SetIterator
  Automatic_Refinement.Automatic_Refinement
begin

fun idx_iteratei_aux 
  :: "('s \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where
  "idx_iteratei_aux get sz i l c f \<sigma> = (
    if i=0 \<or> \<not> c \<sigma> then \<sigma>
    else idx_iteratei_aux get sz (i - 1) l c f (f (get l (sz-i)) \<sigma>)
  )"

declare idx_iteratei_aux.simps[simp del]

lemma idx_iteratei_aux_simps[simp]:
  "i=0 \<Longrightarrow> idx_iteratei_aux get sz i l c f \<sigma> = \<sigma>"
  "\<not>c \<sigma> \<Longrightarrow> idx_iteratei_aux get sz i l c f \<sigma> = \<sigma>"
  "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_iteratei_aux get sz i l c f \<sigma> = idx_iteratei_aux get sz (i - 1) l c f (f (get l (sz-i)) \<sigma>)"
  apply -
  apply (subst idx_iteratei_aux.simps, simp)+
  done

definition "idx_iteratei get sz l c f \<sigma> == idx_iteratei_aux get (sz l) (sz l) l c f \<sigma>"

lemma idx_iteratei_eq_foldli:
  assumes sz: "(sz, length) \<in> arel \<rightarrow> nat_rel"
  assumes get: "(get, (!)) \<in> arel \<rightarrow> nat_rel \<rightarrow> Id"
  assumes "(s,s') \<in> arel"
  shows "(idx_iteratei get sz s, foldli s') \<in> Id" 
proof-
  have size_correct: "\<And>s s'. (s,s') \<in> arel \<Longrightarrow> sz s = length s'"
      using sz[param_fo] by simp
  have get_correct: "\<And>s s' n. (s,s') \<in> arel \<Longrightarrow> get s n = s' ! n"
      using get[param_fo] by simp
  {
    fix n l
    assume A: "Suc n \<le> length l"
    hence B: "length l - Suc n < length l" by simp
    from A have [simp]: "Suc (length l - Suc n) = length l - n" by simp
    from Cons_nth_drop_Suc[OF B, simplified] have 
      "drop (length l - Suc n) l = l!(length l - Suc n)#drop (length l - n) l" 
      by simp
  } note drop_aux=this

  {
    fix s s' c f \<sigma> i
    assume "(s,s') \<in> arel" "i\<le>sz s"
    hence "idx_iteratei_aux get (sz s) i s c f \<sigma> = foldli (drop (sz s - i) s') c f \<sigma>"
    proof (induct i arbitrary: \<sigma>)
      case 0 with size_correct[of s] show ?case by simp
    next
      case (Suc n)
      note S = Suc.prems(1)
      show ?case proof (cases "c \<sigma>")
        case False thus ?thesis by simp
      next
        case [simp, intro!]: True
        show ?thesis using Suc
            by (simp add: size_correct[OF S] get_correct[OF S] drop_aux)
      qed
    qed
  } note aux=this

  show ?thesis
    unfolding idx_iteratei_def[abs_def]
    by (simp, intro ext, simp add: aux[OF \<open>(s,s') \<in> arel\<close>])
qed


text \<open>Misc.\<close>

lemma idx_iteratei_aux_nth_conv_foldli_drop:
  fixes xs :: "'b list"
  assumes "i \<le> length xs"
  shows "idx_iteratei_aux (!) (length xs) i xs c f \<sigma> = foldli (drop (length xs - i) xs) c f \<sigma>"
using assms
proof(induct get\<equiv>"(!) :: 'b list \<Rightarrow> nat \<Rightarrow> 'b" sz\<equiv>"length xs" i xs c f \<sigma> rule: idx_iteratei_aux.induct)
  case (1 i l c f \<sigma>)
  show ?case
  proof(cases "i = 0 \<or> \<not> c \<sigma>")
    case True thus ?thesis
      by(subst idx_iteratei_aux.simps)(auto)
  next
    case False
    hence i: "i > 0" and c: "c \<sigma>" by auto
    hence "idx_iteratei_aux (!) (length l) i l c f \<sigma> = idx_iteratei_aux (!) (length l) (i - 1) l c f (f (l ! (length l - i)) \<sigma>)"
      by(subst idx_iteratei_aux.simps) simp
    also have "\<dots> = foldli (drop (length l - (i - 1)) l) c f (f (l ! (length l - i)) \<sigma>)"
      using \<open>i \<le> length l\<close> i c by -(rule 1, auto)
    also from \<open>i \<le> length l\<close> i
    have "drop (length l - i) l = (l ! (length l - i)) # drop (length l - (i - 1)) l"
      apply (subst Cons_nth_drop_Suc[symmetric])
      apply simp_all
      done
    hence "foldli (drop (length l - (i - 1)) l) c f (f (l ! (length l - i)) \<sigma>) = foldli (drop (length l - i) l) c f \<sigma>"
      using c by simp
    finally show ?thesis .
  qed
qed

lemma idx_iteratei_nth_length_conv_foldli: "idx_iteratei nth length = foldli"
by(rule ext)+(simp add: idx_iteratei_def idx_iteratei_aux_nth_conv_foldli_drop)
end
