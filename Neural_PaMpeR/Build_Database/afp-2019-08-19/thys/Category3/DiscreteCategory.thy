(*  Title:       DiscreteCategory
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2016
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter DiscreteCategory

theory DiscreteCategory
imports Category
begin

  text\<open>
    The locale defined here permits us to construct a discrete category having
    a specified set of objects, assuming that the set does not exhaust the elements
    of its type.  In that case, we have the convenient situation that the arrows of
    the category can be directly identified with the elements of the given set,
    rather than having to pass between the two via tedious coercion maps.
    If it cannot be guaranteed that the given set is not the universal set at its type,
    then the more general discrete category construction defined (using coercions)
    in \<open>FreeCategory\<close> can be used.
\<close>

  locale discrete_category =
    fixes Obj :: "'a set"
    and Null :: 'a
    assumes Null_not_in_Obj: "Null \<notin> Obj"
  begin

    definition comp :: "'a comp"      (infixr "\<cdot>" 55)
    where "y \<cdot> x \<equiv> (if x \<in> Obj \<and> x = y then x else Null)"

    interpretation partial_magma comp
      apply unfold_locales
      using comp_def by metis

    lemma null_char:
    shows "null = Null"
      using comp_def null_def by auto

    lemma ide_char [iff]:
    shows "ide f \<longleftrightarrow> f \<in> Obj"
      using comp_def null_char ide_def Null_not_in_Obj by auto

    lemma domains_char:
    shows "domains f = {x. x \<in> Obj \<and> x = f}"
    proof
      show "{x. x \<in> Obj \<and> x = f} \<subseteq> domains f"
        unfolding domains_def
        using ide_char ide_def by fastforce
      show "domains f \<subseteq> {x. x \<in> Obj \<and> x = f}"
        unfolding domains_def
        using ide_char by (simp add: Collect_mono comp_def null_char)
    qed

    theorem is_category:
    shows "category comp"
      using comp_def
      apply unfold_locales
      using arr_def null_char self_domain_iff_ide ide_char
           apply fastforce
      using null_char self_codomain_iff_ide domains_char codomains_def ide_char
          apply fastforce
         apply (metis not_arr_null null_char)
        apply (metis not_arr_null null_char)
      by auto

  end

  sublocale discrete_category \<subseteq> category comp
    using is_category by auto

  context discrete_category
  begin

    lemma arr_char [iff]:
    shows "arr f \<longleftrightarrow> f \<in> Obj"
      using comp_def comp_cod_arr
      by (metis empty_iff has_codomain_iff_arr not_arr_null null_char self_codomain_iff_ide ide_char)

    lemma dom_char [simp]:
    shows "dom f = (if f \<in> Obj then f else null)"
      using arr_def dom_def arr_char ideD(2) by auto

    lemma cod_char [simp]:
    shows "cod f = (if f \<in> Obj then f else null)"
      using arr_def in_homE cod_def ideD(3) by auto

    lemma comp_char [simp]:
    shows "comp g f = (if f \<in> Obj \<and> f = g then f else null)"
      using comp_def null_char by auto

    lemma is_discrete:
    shows "ide = arr"
      using arr_char ide_char by auto

  end

end
