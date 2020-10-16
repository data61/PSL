section \<open>\isaheader{Generic Algorithms for Sequences}\<close>
theory ListGA
imports "../spec/ListSpec" 
begin

subsection \<open>Iterators\<close>

subsubsection \<open>iteratei (by get, size)\<close>

locale idx_iteratei_loc = 
  list_size + list_get +
  constrains \<alpha> :: "'s \<Rightarrow> 'a list"
  assumes [simp]: "\<And>s. invar s"
begin

  fun idx_iteratei_aux 
    :: "nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
  where
    "idx_iteratei_aux sz i l c f \<sigma> = (
      if i=0 \<or> \<not> c \<sigma> then \<sigma>
      else idx_iteratei_aux sz (i - 1) l c f (f (get l (sz-i)) \<sigma>)
    )"

  declare idx_iteratei_aux.simps[simp del]

  lemma idx_iteratei_aux_simps[simp]:
    "i=0 \<Longrightarrow> idx_iteratei_aux sz i l c f \<sigma> = \<sigma>"
    "\<not>c \<sigma> \<Longrightarrow> idx_iteratei_aux sz i l c f \<sigma> = \<sigma>"
    "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_iteratei_aux sz i l c f \<sigma> = idx_iteratei_aux sz (i - 1) l c f (f (get l (sz-i)) \<sigma>)"
    apply -
    apply (subst idx_iteratei_aux.simps, simp)+
    done

  definition idx_iteratei where 
    "idx_iteratei l c f \<sigma> \<equiv> idx_iteratei_aux (size l) (size l) l c f \<sigma>"

  lemma idx_iteratei_correct:
    shows "idx_iteratei s = foldli (\<alpha> s)" 
  proof -
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
      fix s c f \<sigma> i
      assume "invar s" "i\<le>size s"
      hence "idx_iteratei_aux (size s) i s c f \<sigma> 
        = foldli (drop (size s - i) (\<alpha> s)) c f \<sigma>"
      proof (induct i arbitrary: \<sigma>)
        case 0 with size_correct[of s] show ?case by simp
      next
        case (Suc n)
        note [simp, intro!] = Suc.prems(1)
        show ?case proof (cases "c \<sigma>")
          case False thus ?thesis by simp
        next
          case [simp, intro!]: True
          show ?thesis using Suc by (simp add: get_correct size_correct drop_aux)
        qed
      qed
    } note aux=this

    show ?thesis
      unfolding idx_iteratei_def[abs_def]
      by (auto simp add: fun_eq_iff aux[of _ "size s", simplified])
  qed

  lemmas idx_iteratei_unfold[code_unfold] = idx_iteratei_correct[symmetric]

  subsubsection \<open>reverse\_iteratei (by get, size)\<close>

  fun idx_reverse_iteratei_aux 
    :: "nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
    where
    "idx_reverse_iteratei_aux sz i l c f \<sigma> = (
      if i=0 \<or> \<not> c \<sigma> then \<sigma>
      else idx_reverse_iteratei_aux sz (i - 1) l c f (f (get l (i - 1)) \<sigma>)
    )"

  declare idx_reverse_iteratei_aux.simps[simp del]

  lemma idx_reverse_iteratei_aux_simps[simp]:
    "i=0 \<Longrightarrow> idx_reverse_iteratei_aux sz i l c f \<sigma> = \<sigma>"
    "\<not>c \<sigma> \<Longrightarrow> idx_reverse_iteratei_aux sz i l c f \<sigma> = \<sigma>"
    "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_reverse_iteratei_aux sz i l c f \<sigma> 
    = idx_reverse_iteratei_aux sz (i - 1) l c f (f (get l (i - 1)) \<sigma>)"
    by (subst idx_reverse_iteratei_aux.simps, simp)+

  definition "idx_reverse_iteratei l c f \<sigma> 
    == idx_reverse_iteratei_aux (size l) (size l) l c f \<sigma>"

  lemma idx_reverse_iteratei_correct:
    shows "idx_reverse_iteratei s = foldri (\<alpha> s)"
  proof -
    {
      fix s c f \<sigma> i
      assume "invar s" "i\<le>size s"
      hence "idx_reverse_iteratei_aux (size s) i s c f \<sigma> 
        = foldri (take i (\<alpha> s)) c f \<sigma>"
      proof (induct i arbitrary: \<sigma>)
        case 0 with size_correct[of s] show ?case by simp
      next
        case (Suc n)
        note [simp, intro!] = Suc.prems(1)
        show ?case proof (cases "c \<sigma>")
          case False thus ?thesis by simp
        next
          case [simp, intro!]: True
          show ?thesis using Suc 
            by (simp add: get_correct size_correct take_Suc_conv_app_nth)
        qed
      qed
    } note aux=this

    show ?thesis
      unfolding idx_reverse_iteratei_def[abs_def]
      apply (simp add: fun_eq_iff aux[of _ "size s", simplified])
      apply (simp add: size_correct)
    done
  qed

  lemmas idx_reverse_iteratei_unfold[code_unfold] 
    = idx_reverse_iteratei_correct[symmetric]

end

subsection \<open>Size (by iterator)\<close>

locale it_size_loc = poly_list_iteratei +
  constrains \<alpha> :: "'s \<Rightarrow> 'a list"
begin

  definition it_size :: "'s \<Rightarrow> nat"
    where "it_size l == iterate l (\<lambda>x res. Suc res) (0::nat)"

  lemma it_size_impl: shows "list_size \<alpha> invar it_size"
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (simp add: iterate_correct foldli_foldl)
    done
end

subsubsection \<open>Size (by reverse\_iterator)\<close>

locale rev_it_size_loc = poly_list_rev_iteratei +
  constrains \<alpha> :: "'s \<Rightarrow> 'a list"
begin

  definition rev_it_size :: "'s \<Rightarrow> nat"
    where "rev_it_size l == rev_iterate l (\<lambda>x res. Suc res) (0::nat)"

  lemma rev_it_size_impl:
    shows "list_size \<alpha> invar rev_it_size"
    apply (unfold_locales)
    apply (unfold rev_it_size_def)
    apply (simp add: rev_iterate_correct foldri_foldr)
    done

end

subsection \<open>Get (by iteratori)\<close>
locale it_get_loc = poly_list_iteratei + 
  constrains \<alpha> :: "'s \<Rightarrow> 'a list"
begin

  definition it_get:: "'s \<Rightarrow> nat \<Rightarrow> 'a" 
    where "it_get s i \<equiv> 
      the (snd (iteratei s
                (\<lambda>(i,x). x=None) 
                (\<lambda>x (i,_). if i=0 then (0,Some x) else (i - 1,None)) 
                (i,None)))"

  lemma it_get_correct:
    shows "list_get \<alpha> invar it_get"
  proof 
    fix s i 
    assume "invar s" "i < length (\<alpha> s)"

    define l where "l = \<alpha> s"
    from \<open>i < length (\<alpha> s)\<close>
    show "it_get s i = \<alpha> s ! i"
      unfolding it_get_def iteratei_correct l_def[symmetric]
    proof (induct i arbitrary: l)
      case 0
      then obtain x xs where l_eq[simp]: "l = x # xs" by (cases l, auto)
      thus ?case by simp
    next
      case (Suc i)
      note ind_hyp = Suc(1)
      note Suc_i_le = Suc(2)
      from Suc_i_le obtain x xs 
        where l_eq[simp]: "l = x # xs" by (cases l, auto)

      from ind_hyp [of xs] Suc_i_le
      show ?case by simp
    qed
  qed
end

end
