section \<open>Backwards Compatibility for Version 1\<close>
theory CollectionsV1
imports Collections
begin
  text \<open>
    This theory defines some stuff to establish (partial) backwards
    compatibility with ICF Version 1.
\<close>

  (*
    TODO: Dirty hack to workaround a problem that occurs with sublocale here:
      When declaring
        
  sublocale poly_map_iteratei < v1_iteratei: map_iteratei \<alpha> invar iteratei
    by (rule v1_iteratei_impl)

      Any further 

  interpretation StdMap hm_ops

    will fail with
*** exception TYPE raised (line 414 of "type.ML"):
*** Type variable "?'a" has two distinct sorts
*** ?'a::type
*** ?'a::hashable

  The problem seems difficult to track down, as it, e.g., does not iccur for 
  sets.
*)

  attribute_setup locale_witness_add = \<open>
    Scan.succeed (Locale.witness_add)
\<close> "Add witness for locale instantiation. HACK, use 
      sublocale or interpretation whereever possible!"


  subsection \<open>Iterators\<close>
  text \<open>We define all the monomorphic iterator locales\<close>
  subsubsection "Set"
locale set_iteratei = finite_set \<alpha> invar for \<alpha> :: "'s \<Rightarrow> 'x set" and invar +
  fixes iteratei :: "'s \<Rightarrow> ('x, '\<sigma>) set_iterator"

  assumes iteratei_rule: "invar S \<Longrightarrow> set_iterator (iteratei S) (\<alpha> S)"
begin
  lemma iteratei_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S c f \<sigma>0)"
   apply (rule set_iterator_rule_P [OF iteratei_rule, of S I \<sigma>0 c f P])
   apply simp_all
  done

  lemma iteratei_rule_insert_P:
    "\<lbrakk>
      invar S;
      I {} \<sigma>0;
      !!x it \<sigma>. \<lbrakk> c \<sigma>; x \<in> \<alpha> S - it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert x it) (f x \<sigma>);
      !!\<sigma>. I (\<alpha> S) \<sigma> \<Longrightarrow> P \<sigma>;
      !!\<sigma> it. \<lbrakk> it \<subseteq> \<alpha> S; it \<noteq> \<alpha> S; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S c f \<sigma>0)"
    apply (rule set_iterator_rule_insert_P [OF iteratei_rule, of S I \<sigma>0 c f P])
    apply simp_all
  done

  text \<open>Versions without break condition.\<close>
  lemma iterate_rule_P:
    "\<lbrakk>
      invar S;
      I (\<alpha> S) \<sigma>0;
      !!x it \<sigma>. \<lbrakk> x \<in> it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {x}) (f x \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S (\<lambda>_. True) f \<sigma>0)"
   apply (rule set_iterator_no_cond_rule_P [OF iteratei_rule, of S I \<sigma>0 f P])
   apply simp_all
  done

  lemma iterate_rule_insert_P:
    "\<lbrakk>
      invar S;
      I {} \<sigma>0;
      !!x it \<sigma>. \<lbrakk> x \<in> \<alpha> S - it; it \<subseteq> \<alpha> S; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert x it) (f x \<sigma>);
      !!\<sigma>. I (\<alpha> S) \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei S (\<lambda>_. True) f \<sigma>0)"
    apply (rule set_iterator_no_cond_rule_insert_P [OF iteratei_rule, of S I \<sigma>0 f P])
    apply simp_all
  done
end

lemma set_iteratei_I :
assumes "\<And>s. invar s \<Longrightarrow> set_iterator (iti s) (\<alpha> s)"
shows "set_iteratei \<alpha> invar iti"
proof
  fix s 
  assume invar_s: "invar s"
  from assms(1)[OF invar_s] show it_OK: "set_iterator (iti s) (\<alpha> s)" .
  
  from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_def]]
  show "finite (\<alpha> s)" .
qed

  locale set_iterateoi = ordered_finite_set \<alpha> invar
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) set" and invar
    +
    fixes iterateoi :: "'s \<Rightarrow> ('u,'\<sigma>) set_iterator"
    assumes iterateoi_rule: 
      "invar s \<Longrightarrow> set_iterator_linord (iterateoi s) (\<alpha> s)"
  begin
    lemma iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I (\<alpha> m) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<le>j; 
        \<forall>j\<in>\<alpha> m - it. j\<le>k; 
        it \<subseteq> \<alpha> m; 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> \<alpha> m; 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>\<alpha> m - it. j\<le>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "P (iterateoi m c f \<sigma>0)"  
    using set_iterator_linord_rule_P [OF iterateoi_rule, OF MINV, of I \<sigma>0 c f P,
       OF I0 _ IF] IP II
    by simp

    lemma iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
      assumes MINV: "invar m"
      assumes I0: "I ((\<alpha> m)) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> k \<in> it; \<forall>j\<in>it. k\<le>j; \<forall>j\<in>(\<alpha> m) - it. j\<le>k; it \<subseteq> (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (iterateoi m (\<lambda>_. True) f \<sigma>0)"
      apply (rule iterateoi_rule_P [where I = I])
      apply (simp_all add: assms)
    done
  end

  lemma set_iterateoi_I :
  assumes "\<And>s. invar s \<Longrightarrow> set_iterator_linord (itoi s) (\<alpha> s)"
  shows "set_iterateoi \<alpha> invar itoi"
  proof
    fix s
    assume invar_s: "invar s"
    from assms(1)[OF invar_s] show it_OK: "set_iterator_linord (itoi s) (\<alpha> s)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_linord_def]]
    show "finite (\<alpha> s)" by simp 
  qed

  (* Deprecated *)
  locale set_reverse_iterateoi = ordered_finite_set \<alpha> invar 
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) set" and invar
    +
    fixes reverse_iterateoi :: "'s \<Rightarrow> ('u,'\<sigma>) set_iterator"
    assumes reverse_iterateoi_rule: "
      invar m \<Longrightarrow> set_iterator_rev_linord (reverse_iterateoi m) (\<alpha> m)" 
  begin
    lemma reverse_iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I ((\<alpha> m)) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in>(\<alpha> m) - it. j\<ge>k; 
        it \<subseteq> (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> (\<alpha> m); 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>(\<alpha> m) - it. j\<ge>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (reverse_iterateoi m c f \<sigma>0)"
    using set_iterator_rev_linord_rule_P [OF reverse_iterateoi_rule, OF MINV, of I \<sigma>0 c f P,
       OF I0 _ IF] IP II
    by simp

    lemma reverse_iterateo_rule_P[case_names minv inv0 inv_pres i_complete]:
      assumes MINV: "invar m"
      assumes I0: "I ((\<alpha> m)) \<sigma>0"
      assumes IP: "!!k it \<sigma>. \<lbrakk> 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in> (\<alpha> m) - it. j\<ge>k; 
        it \<subseteq> (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f k \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
    shows "P (reverse_iterateoi m (\<lambda>_. True) f \<sigma>0)"
      apply (rule reverse_iterateoi_rule_P [where I = I])
      apply (simp_all add: assms)
    done
  end

  lemma set_reverse_iterateoi_I :
  assumes "\<And>s. invar s \<Longrightarrow> set_iterator_rev_linord (itoi s) (\<alpha> s)"
  shows "set_reverse_iterateoi \<alpha> invar itoi"
  proof
    fix s
    assume invar_s: "invar s"
    from assms(1)[OF invar_s] show it_OK: "set_iterator_rev_linord (itoi s) (\<alpha> s)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_rev_linord_def]]
    show "finite (\<alpha> s)" by simp 
  qed


  lemma (in poly_set_iteratei) v1_iteratei_impl: 
    "set_iteratei \<alpha> invar iteratei"
    by unfold_locales (rule iteratei_correct)
  lemma (in poly_set_iterateoi) v1_iterateoi_impl: 
    "set_iterateoi \<alpha> invar iterateoi"
    by unfold_locales (rule iterateoi_correct)
  lemma (in poly_set_rev_iterateoi) v1_reverse_iterateoi_impl: 
    "set_reverse_iterateoi \<alpha> invar rev_iterateoi"
    by unfold_locales (rule rev_iterateoi_correct)

  declare (in poly_set_iteratei) v1_iteratei_impl[locale_witness_add]
  declare (in poly_set_iterateoi) v1_iterateoi_impl[locale_witness_add]
  declare (in poly_set_rev_iterateoi) 
    v1_reverse_iterateoi_impl[locale_witness_add]

  (* Commented out, as it causes strange errors of the kind:
    Type variable "?'a" has two distinct sorts

  sublocale poly_set_iteratei < v1_iteratei: set_iteratei \<alpha> invar iteratei
    by (rule v1_iteratei_impl)
  sublocale poly_set_iterateoi < v1_iteratei: set_iterateoi \<alpha> invar iterateoi
    by (rule v1_iterateoi_impl)
  sublocale poly_set_rev_iterateoi 
    < v1_iteratei!: set_reverse_iterateoi \<alpha> invar rev_iterateoi
    by (rule v1_reverse_iterateoi_impl)
    *)

subsubsection "Map"
locale map_iteratei = finite_map \<alpha> invar for \<alpha> :: "'s \<Rightarrow> 'u \<rightharpoonup> 'v" and invar +
  fixes iteratei :: "'s \<Rightarrow> ('u \<times> 'v,'\<sigma>) set_iterator"

  assumes iteratei_rule: "invar m \<Longrightarrow> map_iterator (iteratei m) (\<alpha> m)"
begin

  lemma iteratei_rule_P:
    assumes "invar m"
        and I0: "I (dom (\<alpha> m)) \<sigma>0"
        and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                    \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
        and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
        and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom (\<alpha> m); it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    using map_iterator_rule_P [OF iteratei_rule, of m I \<sigma>0 c f P]
    by (simp_all add: assms)

  lemma iteratei_rule_insert_P:
    assumes  
      "invar m" 
      "I {} \<sigma>0"
      "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> (dom (\<alpha> m) - it); \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
          \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
      "!!\<sigma>. I (dom (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>"
      "!!\<sigma> it. \<lbrakk> it \<subseteq> dom (\<alpha> m); it \<noteq> dom (\<alpha> m); 
               \<not> (c \<sigma>); 
               I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iteratei m c f \<sigma>0)"
    using map_iterator_rule_insert_P [OF iteratei_rule, of m I \<sigma>0 c f P]
    by (simp_all add: assms)

  lemma iterate_rule_P:
    "\<lbrakk>
      invar m;
      I (dom (\<alpha> m)) \<sigma>0;
      !!k v it \<sigma>. \<lbrakk> k \<in> it; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>);
      !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei m (\<lambda>_. True) f \<sigma>0)"
    using iteratei_rule_P [of m I \<sigma>0 "\<lambda>_. True" f P]
    by fast

  lemma iterate_rule_insert_P:
    "\<lbrakk>
      invar m;
      I {} \<sigma>0;
      !!k v it \<sigma>. \<lbrakk> k \<in> (dom (\<alpha> m) - it); \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>);
      !!\<sigma>. I (dom (\<alpha> m)) \<sigma> \<Longrightarrow> P \<sigma>
    \<rbrakk> \<Longrightarrow> P (iteratei m (\<lambda>_. True) f \<sigma>0)"
    using iteratei_rule_insert_P [of m I \<sigma>0 "\<lambda>_. True" f P]
    by fast
end

lemma map_iteratei_I :
  assumes "\<And>m. invar m \<Longrightarrow> map_iterator (iti m) (\<alpha> m)"
  shows "map_iteratei \<alpha> invar iti"
proof
  fix m 
  assume invar_m: "invar m"
  from assms(1)[OF invar_m] show it_OK: "map_iterator (iti m) (\<alpha> m)" .
  
  from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_def]]
  show "finite (dom (\<alpha> m))" by (simp add: finite_map_to_set) 
qed


  locale map_iterateoi = ordered_finite_map \<alpha> invar
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" and invar
    +
    fixes iterateoi :: "'s \<Rightarrow> ('u \<times> 'v,'\<sigma>) set_iterator"
    assumes iterateoi_rule: "
      invar m \<Longrightarrow> map_iterator_linord (iterateoi m) (\<alpha> m)"
  begin
    lemma iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<le>j; 
        \<forall>j\<in>dom (\<alpha> m) - it. j\<le>k; 
        \<alpha> m k = Some v; 
        it \<subseteq> dom (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> dom (\<alpha> m); 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>dom (\<alpha> m) - it. j\<le>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "P (iterateoi m c f \<sigma>0)"
    using map_iterator_linord_rule_P [OF iterateoi_rule, of m I \<sigma>0 c f P] assms
    by simp

    lemma iterateo_rule_P[case_names minv inv0 inv_pres i_complete]: 
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> k \<in> it; \<forall>j\<in>it. k\<le>j; \<forall>j\<in>dom (\<alpha> m) - it. j\<le>k; \<alpha> m k = Some v; it \<subseteq> dom (\<alpha> m); I it \<sigma> \<rbrakk> 
                  \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      shows "P (iterateoi m (\<lambda>_. True) f \<sigma>0)"
    using map_iterator_linord_rule_P [OF iterateoi_rule, of m I \<sigma>0 "\<lambda>_. True" f P] assms
    by simp
  end

  lemma map_iterateoi_I :
  assumes "\<And>m. invar m \<Longrightarrow> map_iterator_linord (itoi m) (\<alpha> m)"
  shows "map_iterateoi \<alpha> invar itoi"
  proof
    fix m 
    assume invar_m: "invar m"
    from assms(1)[OF invar_m] show it_OK: "map_iterator_linord (itoi m) (\<alpha> m)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_map_linord_def]]
    show "finite (dom (\<alpha> m))" by (simp add: finite_map_to_set) 
  qed

  locale map_reverse_iterateoi = ordered_finite_map \<alpha> invar 
    for \<alpha> :: "'s \<Rightarrow> ('u::linorder) \<rightharpoonup> 'v" and invar
    +
    fixes reverse_iterateoi :: "'s \<Rightarrow> ('u \<times> 'v,'\<sigma>) set_iterator"
    assumes reverse_iterateoi_rule: "
      invar m \<Longrightarrow> map_iterator_rev_linord (reverse_iterateoi m) (\<alpha> m)"
  begin
    lemma reverse_iterateoi_rule_P[case_names minv inv0 inv_pres i_complete i_inter]:
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> 
        c \<sigma>; 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in>dom (\<alpha> m) - it. j\<ge>k; 
        \<alpha> m k = Some v; 
        it \<subseteq> dom (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      assumes II: "!!\<sigma> it. \<lbrakk> 
        it \<subseteq> dom (\<alpha> m); 
        it \<noteq> {}; 
        \<not> c \<sigma>; 
        I it \<sigma>; 
        \<forall>k\<in>it. \<forall>j\<in>dom (\<alpha> m) - it. j\<ge>k 
      \<rbrakk> \<Longrightarrow> P \<sigma>"
      shows "P (reverse_iterateoi m c f \<sigma>0)"
    using map_iterator_rev_linord_rule_P [OF reverse_iterateoi_rule, of m I \<sigma>0 c f P] assms
    by simp

    lemma reverse_iterateo_rule_P[case_names minv inv0 inv_pres i_complete]:
      assumes MINV: "invar m"
      assumes I0: "I (dom (\<alpha> m)) \<sigma>0"
      assumes IP: "!!k v it \<sigma>. \<lbrakk> 
        k \<in> it; 
        \<forall>j\<in>it. k\<ge>j; 
        \<forall>j\<in>dom (\<alpha> m) - it. j\<ge>k; 
        \<alpha> m k = Some v; 
        it \<subseteq> dom (\<alpha> m); 
        I it \<sigma> 
      \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      assumes IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      shows "P (reverse_iterateoi m (\<lambda>_. True) f \<sigma>0)"
    using map_iterator_rev_linord_rule_P[OF reverse_iterateoi_rule, of m I \<sigma>0 "\<lambda>_. True" f P] assms
    by simp
  end

  lemma map_reverse_iterateoi_I :
  assumes "\<And>m. invar m \<Longrightarrow> map_iterator_rev_linord (ritoi m) (\<alpha> m)"
  shows "map_reverse_iterateoi \<alpha> invar ritoi"
  proof
    fix m 
    assume invar_m: "invar m"
    from assms(1)[OF invar_m] show it_OK: "map_iterator_rev_linord (ritoi m) (\<alpha> m)" .
  
    from set_iterator_genord.finite_S0 [OF it_OK[unfolded set_iterator_map_rev_linord_def]]
    show "finite (dom (\<alpha> m))" by (simp add: finite_map_to_set) 
  qed


  lemma (in poly_map_iteratei) v1_iteratei_impl: 
    "map_iteratei \<alpha> invar iteratei"
    by unfold_locales (rule iteratei_correct)
  lemma (in poly_map_iterateoi) v1_iterateoi_impl: 
    "map_iterateoi \<alpha> invar iterateoi"
    by unfold_locales (rule iterateoi_correct)
  lemma (in poly_map_rev_iterateoi) v1_reverse_iterateoi_impl: 
    "map_reverse_iterateoi \<alpha> invar rev_iterateoi"
    by unfold_locales (rule rev_iterateoi_correct)


  declare (in poly_map_iteratei) v1_iteratei_impl[locale_witness_add]
  declare (in poly_map_iterateoi) v1_iterateoi_impl[locale_witness_add]
  declare (in poly_map_rev_iterateoi) 
    v1_reverse_iterateoi_impl[locale_witness_add]

  (*
  sublocale poly_map_iteratei < v1_iteratei: map_iteratei \<alpha> invar iteratei
    by (rule v1_iteratei_impl)
  sublocale poly_map_iterateoi < v1_iteratei: map_iterateoi \<alpha> invar iterateoi
    by (rule v1_iterateoi_impl)
  sublocale poly_map_rev_iterateoi 
    < v1_iteratei!: map_reverse_iterateoi \<alpha> invar rev_iterateoi
    by (rule v1_reverse_iterateoi_impl)
    *)

  subsection \<open>Concrete Operation Names\<close>
  text \<open>We define abbreviations to recover the \<open>xx_op\<close>-names\<close>

  (* TODO: This may take long, as Local_Theory.abbrev seems to be really slow *)
  local_setup \<open>let
    val thy = @{theory}
    val ctxt = Proof_Context.init_global thy;
    val pats = [
    "hs","hm",
    "rs","rm",
    "ls","lm","lsi","lmi","lsnd","lss",
    "ts","tm",
    "ias","iam",
    "ahs","ahm",
    "bino",
    "fifo",
    "ft",
    "alprioi",
    "aluprioi",
    "skew"
    ];

    val {const_space, constants, ...} = Sign.consts_of thy |> Consts.dest
    val clist = Name_Space.extern_entries true ctxt const_space constants |> map (apfst #1)

    fun abbrevs_for pat = clist
    |> map_filter (fn (n,_) => case Long_Name.explode n of
        [_,prefix,opname] =>
          if prefix = pat then let 
              val aname = prefix ^ "_" ^ opname
              val rhs = Proof_Context.read_term_abbrev ctxt n
            in SOME (aname,rhs) end
          else NONE
      | _ => NONE);

    fun do_abbrevs pat lthy = let
      val abbrevs = abbrevs_for pat;
    in 
      case abbrevs of [] => (warning ("No stuff found for "^pat); lthy)
      | _ => let 
        (*val _ = tracing ("Defining " ^ pat ^ "_xxx ...");*)
        val lthy = fold (fn (name,rhs) =>
          Local_Theory.abbrev 
            Syntax.mode_input 
            ((Binding.name name,NoSyn),rhs) #> #2
        ) abbrevs lthy
        (*val _ = tracing "Done";*)
      in lthy end
    end
  in
    fold do_abbrevs pats
  end

\<close>


lemmas hs_correct = hs.correct
lemmas hm_correct = hm.correct
lemmas rs_correct = rs.correct
lemmas rm_correct = rm.correct
lemmas ls_correct = ls.correct
lemmas lm_correct = lm.correct
lemmas lsi_correct = lsi.correct
lemmas lmi_correct = lmi.correct
lemmas lsnd_correct = lsnd.correct
lemmas lss_correct = lss.correct
lemmas ts_correct = ts.correct
lemmas tm_correct = tm.correct
lemmas ias_correct = ias.correct
lemmas iam_correct = iam.correct
lemmas ahs_correct = ahs.correct
lemmas ahm_correct = ahm.correct
lemmas bino_correct = bino.correct
lemmas fifo_correct = fifo.correct
lemmas ft_correct = ft.correct
lemmas alprioi_correct = alprioi.correct
lemmas aluprioi_correct = aluprioi.correct
lemmas skew_correct = skew.correct


locale list_enqueue = list_appendr
locale list_dequeue = list_removel

locale list_push = list_appendl
locale list_pop = list_remover
locale list_top = list_leftmost
locale list_bot = list_rightmost

instantiation rbt :: ("{equal,linorder}",equal) equal 
begin
  (*definition equal_rbt :: "('a,'b) RBT.rbt \<Rightarrow> _" where "equal_rbt \<equiv> (=)"*)

  definition "equal_class.equal (r :: ('a, 'b) rbt) r' 
    == RBT.impl_of r = RBT.impl_of r'"


  instance
    apply intro_classes
    apply (simp add: equal_rbt_def RBT.impl_of_inject)
    done
end

end
