(*  Title:       Iterators over Finite Sets
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>\isaheader{Iterators over Finite Sets}\<close>
theory SetIterator
imports 
  Automatic_Refinement.Misc 
  Automatic_Refinement.Foldi 
  (*"../../Refine_Monadic/Refine_Monadic"*)
begin

text \<open>When reasoning about finite sets, it is often handy to be able to iterate over the elements
  of the set. If the finite set is represented by a list, the @{term fold} operation can be used.
  For general finite sets, the order of elements is not fixed though. Therefore, nondeterministic
  iterators are introduced in this theory.\<close>

subsection \<open>General Iterators\<close>

type_synonym ('x,'\<sigma>) set_iterator = "('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('x\<Rightarrow>'\<sigma>\<Rightarrow>'\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"

locale set_iterator_genord =
  fixes iti::"('x,'\<sigma>) set_iterator" 
    and S0::"'x set" 
    and R::"'x \<Rightarrow> 'x \<Rightarrow> bool"
  assumes foldli_transform:
    "\<exists>l0. distinct l0 \<and> S0 = set l0 \<and> sorted_wrt R l0 \<and> iti = foldli l0"
begin
  text \<open>Let's prove some trivial lemmata to show that the formalisation agrees with
          the view of iterators described above.\<close>
  lemma set_iterator_weaken_R :
    "(\<And>x y. \<lbrakk>x \<in> S0; y \<in> S0; R x y\<rbrakk> \<Longrightarrow> R' x y) \<Longrightarrow> 
             set_iterator_genord iti S0 R'"
    by (metis set_iterator_genord.intro foldli_transform sorted_wrt_mono_rel)

  lemma finite_S0 :
    shows "finite S0"
    by (metis finite_set foldli_transform)

  lemma iti_stop_rule_cond :
    assumes not_c: "\<not>(c \<sigma>)"
    shows "iti c f \<sigma> = \<sigma>"
  proof -
    from foldli_transform obtain l0 where l0_props:
      "iti c = foldli l0 c" by blast
    with foldli_not_cond [of c \<sigma> l0 f, OF not_c]
    show ?thesis by simp
  qed

  lemma iti_stop_rule_emp :
    assumes S0_emp: "S0 = {}"
    shows "iti c f \<sigma> = \<sigma>"
  proof -
    from foldli_transform obtain l0 where l0_props:
      "S0 = set l0" "iti c = foldli l0 c" by blast
    with foldli.simps(1) [of c f \<sigma>] S0_emp
    show ?thesis by simp
  qed

  text \<open>Reducing everything to folding is cumbersome. Let's
          define a few high-level inference rules.\<close>

  lemma iteratei_rule_P:
    assumes 
      "I S0 \<sigma>0"
      "\<And>S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0; 
                 \<forall>y\<in>S - {x}. R x y; \<forall>y\<in>S0 - S. R y x\<rbrakk> 
                 \<Longrightarrow> I (S - {x}) (f x \<sigma>)"
      "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      "\<And>\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> {}; \<not> c \<sigma>; I S \<sigma>;
               \<forall>x\<in>S. \<forall>y\<in>S0-S. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iti c f \<sigma>0)"
  proof -
    { fix P I \<sigma>0 f
      assume
        I: "I S0 \<sigma>0" and 
        R: "\<And>S \<sigma> x. \<lbrakk>c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0; \<forall>y\<in>S-{x}. R x y\<rbrakk> \<Longrightarrow> I (S - {x}) (f x \<sigma>)" and
        C1: "I {} (iti c f \<sigma>0) \<Longrightarrow> P" and
        C2:"\<And>S. \<lbrakk>S \<subseteq> S0; S \<noteq> {}; \<not> c (iti c f \<sigma>0); I S (iti c f \<sigma>0)\<rbrakk> \<Longrightarrow> P"

      from foldli_transform obtain l0 where l0_props:
         "distinct l0" "S0 = set l0" "sorted_wrt R l0"  "iti c = foldli l0 c" by auto

      from I R  
      have "I {} (iti c f \<sigma>0) \<or> 
          (\<exists>S. S \<subseteq> S0 \<and> S \<noteq> {} \<and> 
               \<not> (c (iti c f \<sigma>0)) \<and> 
               I S (iti c f \<sigma>0))" 
        unfolding l0_props using l0_props(1,3)
      proof (induct l0 arbitrary: \<sigma>0)
        case Nil thus ?case by simp
      next
        case (Cons x l0)
        note ind_hyp = Cons(1)
        note I_x_l0 = Cons(2)
        note step = Cons(3)
        from Cons(4) have dist_l0: "distinct l0" and x_nin_l0: "x \<notin> set l0" by simp_all
        from Cons(5) have R_l0: "\<forall>y\<in>set l0. R x y" and 
                          sort_l0: "sorted_wrt R l0" by simp_all

        show ?case
        proof (cases "c \<sigma>0")
          case False
          with I_x_l0 show ?thesis
            apply (rule_tac disjI2)
            apply (rule_tac exI[where x="set (x # l0)"])
            apply (simp)
          done
        next
          case True note c_\<sigma>0 = this

          from step[of \<sigma>0 x "set (x # l0)"] I_x_l0 R_l0 c_\<sigma>0 x_nin_l0
          have step': "I (set l0) (f x \<sigma>0)"
            by (simp_all add: Ball_def)

          from ind_hyp [OF step' step dist_l0 sort_l0]
          have "I {} (foldli l0 c f (f x \<sigma>0)) \<or> 
                (\<exists>S. S \<subseteq> set l0 \<and> S \<noteq> {} \<and>
                \<not> c (foldli l0 c f (f x \<sigma>0)) \<and> I S (foldli l0 c f (f x \<sigma>0)))" 
            by (fastforce)
          thus ?thesis
            by (simp add: c_\<sigma>0 subset_iff) metis
        qed
      qed
      with C1 C2 have "P" by blast
    } note aux = this

    from assms
    show ?thesis 
      apply (rule_tac aux [of "\<lambda>S \<sigma>. I S \<sigma> \<and> (\<forall>x\<in>S. \<forall>y\<in>S0-S. R y x)" \<sigma>0 f])
      apply auto
    done
  qed

  text \<open>Instead of removing elements one by one from the invariant, adding them is sometimes more natural.\<close>
  lemma iteratei_rule_insert_P:
  assumes pre :
      "I {} \<sigma>0"
      "\<And>S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; \<forall>y\<in>(S0 - S) - {x}. R x y;
                 \<forall>y\<in>S. R y x\<rbrakk> 
                  \<Longrightarrow> I (insert x S) (f x \<sigma>)"
      "\<And>\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>"
      "\<And>\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> S0; 
              \<not> (c \<sigma>); I S \<sigma>; \<forall>x\<in>S0-S. \<forall>y\<in>S. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (iti c f \<sigma>0)"
  proof -
    let ?I' = "\<lambda>S \<sigma>. I (S0 - S) \<sigma>"

    have pre1: 
      "!!\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> {}; \<not> (c \<sigma>); ?I' S \<sigma>;
             \<forall>x\<in>S. \<forall>y\<in>S0-S. R y x\<rbrakk> \<Longrightarrow> P \<sigma>"
    proof -
      fix S \<sigma>
      assume AA: 
        "S \<subseteq> S0" "S \<noteq> {}"
        "\<not> (c \<sigma>)" 
        "?I' S \<sigma>" "\<forall>x\<in>S. \<forall>y\<in>S0-S. R y x"
      with pre(4) [of "S0 - S"]
      show "P \<sigma>" by auto
    qed

    have pre2 :"\<And>x S \<sigma>. \<lbrakk>c \<sigma>; x \<in> S; S \<subseteq> S0; ?I' S \<sigma>; \<forall>y\<in>S - {x}. R x y; \<forall>y\<in>S0-S. R y x \<rbrakk> \<Longrightarrow> ?I' (S - {x}) (f x \<sigma>)"
    proof -
      fix x S \<sigma>
      assume AA : "c \<sigma>" "x \<in> S" "S \<subseteq> S0" "?I' S \<sigma>" "\<forall>y\<in>S - {x}. R x y" "\<forall>y\<in>S0 - S. R y x" 

      from AA(2) AA(3) have "S0 - (S - {x}) = insert x (S0 - S)" "S0 - (S0 - S) = S" by auto
      moreover 
      note pre(2) [of \<sigma> x "S0 - S"] AA
      ultimately show "?I' (S - {x}) (f x \<sigma>)"
        by auto
    qed

    show "P (iti c f \<sigma>0)" 
      apply (rule iteratei_rule_P [of ?I' \<sigma>0 c f P])
      apply (simp add: pre)
      apply (rule pre2) apply simp_all
      apply (simp add: pre(3))
      apply (simp add: pre1)
    done
  qed

  text \<open>Show that iti without interruption is related to fold\<close>
  lemma iti_fold: 
  assumes lc_f: "comp_fun_commute f"
    shows "iti (\<lambda>_. True) f \<sigma>0 = Finite_Set.fold f \<sigma>0 S0"
  proof (rule iteratei_rule_insert_P [where I = "\<lambda>X \<sigma>'. \<sigma>' = Finite_Set.fold f \<sigma>0 X"])
    fix S \<sigma> x
    assume "x \<in> S0 - S" "S \<subseteq> S0" and \<sigma>_eq: "\<sigma> = Finite_Set.fold f \<sigma>0 S"
    from finite_S0 \<open>S \<subseteq> S0\<close> have fin_S: "finite S" by (metis finite_subset)
    from \<open>x \<in> S0 - S\<close> have x_nin_S: "x \<notin> S" by simp
    note fold_eq = comp_fun_commute.fold_insert [OF lc_f fin_S x_nin_S]

    show "f x \<sigma> = Finite_Set.fold f \<sigma>0 (insert x S)" 
      by (simp add: fold_eq \<sigma>_eq)
  qed simp_all
end


subsection \<open>Iterators over Maps\<close>

type_synonym ('k,'v,'\<sigma>) map_iterator = "('k\<times>'v,'\<sigma>) set_iterator"

text \<open>Iterator over the key-value pairs of a finite map are called iterators over maps.\<close>
abbreviation "map_iterator_genord it m R \<equiv> set_iterator_genord it (map_to_set m) R"

subsection \<open>Unordered Iterators\<close>

text \<open>Often one does not care about the order in which the elements are processed. 
        Therefore, the selection function can be set to not impose any further restrictings.
        This leads to considerably simpler theorems.\<close>

definition "set_iterator it S0 \<equiv> set_iterator_genord it S0 (\<lambda>_ _. True)"
abbreviation "map_iterator it m \<equiv> set_iterator it (map_to_set m)"

lemma set_iterator_intro :
    "set_iterator_genord it S0 R \<Longrightarrow> set_iterator it S0"
unfolding set_iterator_def
apply (rule set_iterator_genord.set_iterator_weaken_R [where R = R])
apply simp_all
done

lemma set_iterator_no_cond_rule_P:
"\<lbrakk> set_iterator it S0;
   I S0 \<sigma>0;
   !!S \<sigma> x. \<lbrakk> x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> \<Longrightarrow> I (S - {x}) (f x \<sigma>);
   !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it (\<lambda>_. True) f \<sigma>0)"
unfolding set_iterator_def
using set_iterator_genord.iteratei_rule_P [of it S0 "\<lambda>_ _. True" I \<sigma>0 "\<lambda>_. True" f P]
by simp 

lemma set_iterator_no_cond_rule_insert_P:
"\<lbrakk> set_iterator it S0;
   I {} \<sigma>0;
   !!S \<sigma> x. \<lbrakk> x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0 \<rbrakk>  \<Longrightarrow> I (insert x S) (f x \<sigma>);
   !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it (\<lambda>_. True) f \<sigma>0)"
unfolding set_iterator_def
using set_iterator_genord.iteratei_rule_insert_P [of it S0 "\<lambda>_ _. True" I \<sigma>0 "\<lambda>_. True" f P]
by simp 

lemma set_iterator_rule_P:
"\<lbrakk> set_iterator it S0;
   I S0 \<sigma>0;
   !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> \<Longrightarrow> I (S - {x}) (f x \<sigma>);
   !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
   !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
unfolding set_iterator_def
using set_iterator_genord.iteratei_rule_P [of it S0 "\<lambda>_ _. True" I \<sigma>0 c f P]
by simp 

lemma set_iterator_rule_insert_P:
"\<lbrakk> set_iterator it S0;
   I {} \<sigma>0;
   !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0 \<rbrakk>  \<Longrightarrow> I (insert x S) (f x \<sigma>);
   !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
   !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
unfolding set_iterator_def
using set_iterator_genord.iteratei_rule_insert_P [of it S0 "\<lambda>_ _. True" I \<sigma>0 c f P]
by simp  


text\<open>The following rules is adapted for maps. Instead of a set of key-value pairs the invariant
       now only sees the keys.\<close>
lemma map_iterator_genord_rule_P:
  assumes "map_iterator_genord it m R"
      and I0: "I (dom m) \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; m k = Some v; it \<subseteq> dom m; I it \<sigma>; 
                             \<forall>k' v'. k' \<in> it-{k} \<and> m k' = Some v' \<longrightarrow> R (k, v) (k', v');
                             \<forall>k' v'. k' \<notin> it \<and> m k' = Some v' \<longrightarrow> R (k', v') (k, v)\<rbrakk> \<Longrightarrow> 
                            I (it - {k}) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma>;
                         \<forall>k v k' v'. k \<notin> it \<and> m k = Some v \<and> k' \<in> it \<and> m k' = Some v' \<longrightarrow> 
                                     R (k, v) (k', v') \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (it c f \<sigma>0)"
proof (rule set_iterator_genord.iteratei_rule_P [of it "map_to_set m" R "\<lambda>S \<sigma>. I (fst ` S) \<sigma>" \<sigma>0 c f P])
  show "map_iterator_genord it m R" by fact
next
  show "I (fst ` map_to_set m) \<sigma>0" using I0 by (simp add: map_to_set_dom[symmetric])
next
  fix \<sigma>
  assume "I (fst ` {}) \<sigma>"
  with IF show "P \<sigma>" by simp
next
  fix \<sigma> S
  assume "S \<subseteq> map_to_set m" "S \<noteq> {}" "\<not> c \<sigma>" "I (fst ` S) \<sigma>"  
         and R_prop: "\<forall>x\<in>S. \<forall>y\<in>map_to_set m - S. R y x"
  let ?S' = "fst ` S"

  show "P \<sigma>"
  proof (rule II [where it = ?S'])
    from \<open>S \<subseteq> map_to_set m\<close>
    show "?S' \<subseteq> dom m"
      unfolding map_to_set_dom
      by auto
  next
    from \<open>S \<noteq> {}\<close> show "?S' \<noteq> {}" by auto
  next
    show "\<not> (c \<sigma>)" by fact
  next
    show "I (fst ` S) \<sigma>" by fact
  next
    show "\<forall>k v k' v'.
       k \<notin> fst ` S \<and>
       m k = Some v \<and>
       k' \<in> fst ` S \<and> m k' = Some v' \<longrightarrow>
       R (k, v) (k', v')" 
    proof (intro allI impI, elim conjE )
      fix k v k' v'
      assume pre_k: "k \<notin> fst ` S" "m k = Some v"
      assume pre_k': "k' \<in> fst ` S" "m k' = Some v'"

      from \<open>S \<subseteq> map_to_set m\<close> pre_k' 
      have kv'_in: "(k', v') \<in> S"
        unfolding map_to_set_def by auto

      from \<open>S \<subseteq> map_to_set m\<close> pre_k
      have kv_in: "(k, v) \<in> map_to_set m - S"
        unfolding map_to_set_def 
        by (auto simp add: image_iff)

      from R_prop kv_in kv'_in
      show "R (k, v) (k',v')" by simp
    qed
  qed
next
  fix \<sigma> S kv
  assume "S \<subseteq> map_to_set m" "kv \<in> S" "c \<sigma>" and I_S': "I (fst ` S) \<sigma>" and 
         R_S: "\<forall>kv'\<in>S - {kv}. R kv kv'" and
         R_not_S: "\<forall>kv'\<in>map_to_set m - S. R kv' kv"
  let ?S' = "fst ` S" 
  obtain k v where kv_eq[simp]: "kv = (k, v)" by (rule prod.exhaust)

  have "I (fst ` S - {k}) (f (k, v) \<sigma>)"
  proof (rule IP)
    show "c \<sigma>" by fact
  next
    from \<open>kv \<in> S\<close> show "k \<in> ?S'" by (auto simp add: image_iff Bex_def)
  next
    from \<open>kv \<in> S\<close> \<open>S \<subseteq> map_to_set m\<close> 
    have "kv \<in> map_to_set m" by auto
    thus m_k_eq: "m k = Some v" unfolding map_to_set_def by simp
  next
    from \<open>S \<subseteq> map_to_set m\<close>
    show S'_subset: "?S' \<subseteq> dom m"
      unfolding map_to_set_dom
      by auto
  next
    show "I (fst ` S) \<sigma>" by fact
  next
    from \<open>S \<subseteq> map_to_set m\<close> \<open>kv \<in> S\<close>
    have S_simp: "{(k', v'). k' \<in> (fst ` S) - {k} \<and> m k' = Some v'} = S - {kv}"
      unfolding map_to_set_def subset_iff
      apply (auto simp add: image_iff Bex_def)
      apply (metis option.inject)
    done

    from R_S[unfolded S_simp[symmetric]] R_not_S
    show "\<forall>k' v'. k' \<in> fst ` S - {k} \<and> m k' = Some v' \<longrightarrow>
                  R (k, v) (k', v') " 
      by simp
  next
    from \<open>S \<subseteq> map_to_set m\<close> R_not_S
    show "\<forall>k' v'. k' \<notin> fst ` S \<and> m k' = Some v' \<longrightarrow> R (k', v') (k, v)" 
      apply (simp add: Ball_def map_to_set_def subset_iff image_iff)
      apply metis
    done
  qed

  moreover 
    from \<open>S \<subseteq> map_to_set m\<close> \<open>kv \<in> S\<close>
    have "fst ` (S - {kv}) = fst ` S - {k}"
      apply (simp add: set_eq_iff image_iff Bex_def map_to_set_def subset_iff)
      apply (metis option.inject)
    done

  ultimately show "I (fst ` (S - {kv})) (f kv \<sigma>)" by simp
qed

lemma map_iterator_genord_rule_insert_P:
  assumes "map_iterator_genord it m R"
      and I0: "I {} \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> dom m - it; m k = Some v; it \<subseteq> dom m; I it \<sigma>; 
                             \<forall>k' v'. k' \<in> (dom m - it) - {k} \<and> m k' = Some v' \<longrightarrow> R (k, v) (k', v');
                             \<forall>k' v'. k' \<in> it \<and> m k' = Some v' \<longrightarrow> 
                               R (k', v') (k, v)\<rbrakk> \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> dom m; \<not> c \<sigma>; I it \<sigma>;
                         \<forall>k v k' v'. k \<in> it \<and> m k = Some v \<and> k' \<notin> it \<and> m k' = Some v' \<longrightarrow> 
                                     R (k, v) (k', v') \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (it c f \<sigma>0)"
proof (rule map_iterator_genord_rule_P [of it m R "\<lambda>S \<sigma>. I (dom m - S) \<sigma>"])
  show "map_iterator_genord it m R" by fact
next
  show "I (dom m - dom m) \<sigma>0" using I0 by simp
next
  fix \<sigma>
  assume "I (dom m - {}) \<sigma>"
  with IF show "P \<sigma>" by simp
next
  fix \<sigma> it
  assume assms: "it \<subseteq> dom m" "it \<noteq> {}" "\<not> c \<sigma>" "I (dom m - it) \<sigma>"
                "\<forall>k v k' v'. k \<notin> it \<and> m k = Some v \<and> k' \<in> it \<and> m k' = Some v' \<longrightarrow>
                             R (k, v) (k', v')"
  from assms have "dom m - it \<noteq> dom m" by auto
  with II[of "dom m - it" \<sigma>] assms
  show "P \<sigma>" 
    apply (simp add: subset_iff dom_def)
    apply (metis option.simps(2))
  done
next
  fix k v it \<sigma>
  assume assms: "c \<sigma>" "k \<in> it" "m k = Some v" "it \<subseteq> dom m" "I (dom m - it) \<sigma>"
                "\<forall>k' v'. k' \<in> it - {k} \<and> m k' = Some v' \<longrightarrow> R (k, v) (k', v')"
                "\<forall>k' v'. k' \<notin> it \<and> m k' = Some v' \<longrightarrow> R (k', v') (k, v)"

  hence "insert k (dom m - it) = (dom m - (it - {k}))" "dom m - (dom m - it) = it" by auto
  with assms IP[of \<sigma> k "dom m - it" v]
  show "I (dom m - (it - {k})) (f (k, v) \<sigma>)" by (simp_all add: subset_iff)
qed

lemma map_iterator_rule_P:
  assumes "map_iterator it m"
      and I0: "I (dom m) \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; m k = Some v; it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (it c f \<sigma>0)"
using assms map_iterator_genord_rule_P[of it m "\<lambda>_ _. True" I \<sigma>0 c f P]
unfolding set_iterator_def
by simp

lemma map_iterator_rule_insert_P:
  assumes "map_iterator it m"
      and I0: "I {} \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> dom m - it; m k = Some v; it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> dom m; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (it c f \<sigma>0)"
using assms map_iterator_genord_rule_insert_P[of it m "\<lambda>_ _. True" I \<sigma>0 c f P]
unfolding set_iterator_def
by simp

lemma map_iterator_no_cond_rule_P:
  assumes "map_iterator it m"
      and I0: "I (dom m) \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> k \<in> it; m k = Some v; it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (it (\<lambda>_. True) f \<sigma>0)"
using assms map_iterator_genord_rule_P[of it m "\<lambda>_ _. True" I \<sigma>0 "\<lambda>_. True" f P]
unfolding set_iterator_def
by simp

lemma map_iterator_no_cond_rule_insert_P:
  assumes "map_iterator it m"
      and I0: "I {} \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> k \<in> dom m - it; m k = Some v; it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (it (\<lambda>_. True) f \<sigma>0)"
using assms map_iterator_genord_rule_insert_P[of it m "\<lambda>_ _. True" I \<sigma>0 "\<lambda>_. True" f P]
unfolding set_iterator_def
by simp


subsection \<open>Ordered Iterators\<close>

text \<open>Selecting according to a linear order is another case that is interesting. 
 Ordered iterators over maps, i.\,e.\ iterators over key-value pairs,
 use an order on the keys.\<close>

context linorder begin
  definition "set_iterator_linord it S0 
    \<equiv> set_iterator_genord it S0 (\<le>)"
  definition "set_iterator_rev_linord it S0 
    \<equiv> set_iterator_genord it S0 (\<ge>)"
  definition "set_iterator_map_linord it S0 \<equiv> 
     set_iterator_genord it S0 (\<lambda>(k,_) (k',_). k\<le>k')"
  definition "set_iterator_map_rev_linord it S0 \<equiv> 
     set_iterator_genord it S0 (\<lambda>(k,_) (k',_). k\<ge>k')"
  abbreviation "map_iterator_linord it m \<equiv> 
    set_iterator_map_linord it (map_to_set m)"
  abbreviation "map_iterator_rev_linord it m \<equiv> 
    set_iterator_map_rev_linord it (map_to_set m)"

  lemma set_iterator_linord_rule_P:
  "\<lbrakk> set_iterator_linord it S0;
     I S0 \<sigma>0;
     !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0; \<And>x'. x' \<in> S0-S \<Longrightarrow> x' \<le> x; \<And>x'. x' \<in> S \<Longrightarrow> x \<le> x'\<rbrakk> \<Longrightarrow> I (S - {x}) (f x \<sigma>);
     !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> (\<And>x x'. \<lbrakk>x \<in> S; x' \<in> S0-S\<rbrakk> \<Longrightarrow> x' \<le> x) \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_linord_def
  apply (rule set_iterator_genord.iteratei_rule_P [of it S0 "(\<le>)" I \<sigma>0 c f P])
  apply (simp_all add: Ball_def)
  apply (metis order_refl)
  done

  lemma set_iterator_linord_rule_insert_P:
  "\<lbrakk> set_iterator_linord it S0;
     I {} \<sigma>0;
     !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; \<And>x'. x' \<in> S \<Longrightarrow> x' \<le> x; \<And>x'. x' \<in> S0 - S \<Longrightarrow> x \<le> x'\<rbrakk>  \<Longrightarrow> I (insert x S) (f x \<sigma>);
     !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow> (\<And>x x'. \<lbrakk>x \<in> S0-S; x' \<in> S\<rbrakk> \<Longrightarrow> x' \<le> x) \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_linord_def
  apply (rule set_iterator_genord.iteratei_rule_insert_P [of it S0 "(\<le>)" I \<sigma>0 c f P])
  apply (simp_all add: Ball_def)
  apply (metis order_refl)
  done

  lemma set_iterator_rev_linord_rule_P:
  "\<lbrakk> set_iterator_rev_linord it S0;
     I S0 \<sigma>0;
     !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0; \<And>x'. x' \<in> S0-S \<Longrightarrow> x \<le> x'; \<And>x'. x' \<in> S \<Longrightarrow> x' \<le> x\<rbrakk> \<Longrightarrow> I (S - {x}) (f x \<sigma>);
     !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> (\<And>x x'. \<lbrakk>x \<in> S; x' \<in> S0-S\<rbrakk> \<Longrightarrow> x \<le> x') \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_rev_linord_def
  apply (rule set_iterator_genord.iteratei_rule_P [of it S0 "(\<ge>)" I \<sigma>0 c f P])
  apply (simp_all add: Ball_def)
  apply (metis order_refl)
  done

  lemma set_iterator_rev_linord_rule_insert_P:
  "\<lbrakk> set_iterator_rev_linord it S0;
     I {} \<sigma>0;
     !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; \<And>x'. x' \<in> S \<Longrightarrow> x \<le> x'; \<And>x'. x' \<in> S0 - S \<Longrightarrow> x' \<le> x\<rbrakk>  \<Longrightarrow> I (insert x S) (f x \<sigma>);
     !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow>  (\<And>x x'. \<lbrakk>x \<in> S0-S; x' \<in> S\<rbrakk> \<Longrightarrow> x \<le> x') \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_rev_linord_def
  apply (rule set_iterator_genord.iteratei_rule_insert_P [of it S0 "(\<ge>)" I \<sigma>0 c f P])
  apply (simp_all add: Ball_def)
  apply (metis order_refl)
  done


  lemma set_iterator_map_linord_rule_P:
  "\<lbrakk> set_iterator_map_linord it S0;
     I S0 \<sigma>0;
     !!S \<sigma> k v. \<lbrakk> c \<sigma>; (k, v) \<in> S; I S \<sigma>; S \<subseteq> S0; \<And>k' v'. (k', v') \<in> S0-S \<Longrightarrow> k' \<le> k;
                  \<And>k' v'. (k', v') \<in> S \<Longrightarrow> k \<le> k'\<rbrakk> \<Longrightarrow> I (S - {(k,v)}) (f (k,v) \<sigma>);
     !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> (\<And>k v k' v'. \<lbrakk>(k, v) \<in> S0-S; (k', v') \<in> S\<rbrakk> \<Longrightarrow> k \<le> k') \<Longrightarrow>
         \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_map_linord_def
  apply (rule set_iterator_genord.iteratei_rule_P 
    [of it S0 "(\<lambda>(k,_) (k',_). k \<le> k')" I \<sigma>0 c f P])
  apply simp_all
  apply (auto simp add: Ball_def)
  apply (metis order_refl)
  apply metis
  done

  lemma set_iterator_map_linord_rule_insert_P:
  "\<lbrakk> set_iterator_map_linord it S0;
     I {} \<sigma>0;
     !!S \<sigma> k v. \<lbrakk> c \<sigma>; (k, v) \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; \<And>k' v'. (k', v') \<in> S \<Longrightarrow> k' \<le> k;
                  \<And>k' v'. (k',v') \<in> S0 - S \<Longrightarrow> k \<le> k'\<rbrakk>  \<Longrightarrow> I (insert (k,v) S) (f (k,v) \<sigma>);
     !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow> (\<And>k v k' v'. \<lbrakk>(k, v) \<in> S; (k', v') \<in> S0-S\<rbrakk> \<Longrightarrow> k \<le> k') \<Longrightarrow>
            \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_map_linord_def
  apply (rule set_iterator_genord.iteratei_rule_insert_P 
    [of it S0 "(\<lambda>(k,_) (k',_). k \<le> k')" I \<sigma>0 c f P])
  apply simp_all
  apply (auto simp add: Ball_def)
  apply (metis order_refl)
  apply metis
  done

  lemma set_iterator_map_rev_linord_rule_P:
  "\<lbrakk> set_iterator_map_rev_linord it S0;
     I S0 \<sigma>0;
     !!S \<sigma> k v. \<lbrakk> c \<sigma>; (k, v) \<in> S; I S \<sigma>; S \<subseteq> S0; \<And>k' v'. (k', v') \<in> S0-S \<Longrightarrow> k \<le> k';
                  \<And>k' v'. (k', v') \<in> S \<Longrightarrow> k' \<le> k\<rbrakk> \<Longrightarrow> I (S - {(k,v)}) (f (k,v) \<sigma>);
     !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> (\<And>k v k' v'. \<lbrakk>(k, v) \<in> S0-S; (k', v') \<in> S\<rbrakk> \<Longrightarrow> k' \<le> k) \<Longrightarrow> 
            \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_map_rev_linord_def
  apply (rule set_iterator_genord.iteratei_rule_P 
    [of it S0 "(\<lambda>(k,_) (k',_). k \<ge> k')" I \<sigma>0 c f P])
  apply simp_all
  apply (auto simp add: Ball_def)
  apply (metis order_refl)
  apply metis
  done

  lemma set_iterator_map_rev_linord_rule_insert_P:
  "\<lbrakk> set_iterator_map_rev_linord it S0;
     I {} \<sigma>0;
     !!S \<sigma> k v. \<lbrakk> c \<sigma>; (k, v) \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; \<And>k' v'. (k', v') \<in> S \<Longrightarrow> k \<le> k';
                 \<And>k' v'. (k',v') \<in> S0 - S \<Longrightarrow> k' \<le> k\<rbrakk>  \<Longrightarrow> I (insert (k,v) S) (f (k,v) \<sigma>);
     !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
     !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow> (\<And>k v k' v'. \<lbrakk>(k, v) \<in> S; (k', v') \<in> S0-S\<rbrakk> \<Longrightarrow> k' \<le> k) \<Longrightarrow> 
            \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
   \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
  unfolding set_iterator_map_rev_linord_def
  apply (rule set_iterator_genord.iteratei_rule_insert_P 
    [of it S0 "(\<lambda>(k,_) (k',_). k \<ge> k')" I \<sigma>0 c f P])
  apply simp_all
  apply (auto simp add: Ball_def)
  apply (metis order_refl)
  apply metis
  done


  lemma map_iterator_linord_rule_P:
    assumes "map_iterator_linord it m"
        and I0: "I (dom m) \<sigma>0"
        and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; m k = Some v; it \<subseteq> dom m; I it \<sigma>;
                 \<And>k'. k' \<in> it \<Longrightarrow> k \<le> k'; 
                 \<And>k'. k' \<in> (dom m)-it \<Longrightarrow> k' \<le> k\<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
        and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
        and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma>;
                  \<And>k k'. \<lbrakk>k \<in> (dom m)-it; k' \<in> it\<rbrakk> \<Longrightarrow> k \<le> k'\<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (it c f \<sigma>0)"
  using assms
  unfolding set_iterator_map_linord_def
  by (rule map_iterator_genord_rule_P) auto

  lemma map_iterator_linord_rule_insert_P:
    assumes "map_iterator_linord it m"
        and I0: "I {} \<sigma>0"
        and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> dom m - it; m k = Some v; it \<subseteq> dom m; I it \<sigma>;
                 \<And>k'. k' \<in> (dom m - it) \<Longrightarrow> k \<le> k'; 
                 \<And>k'. k' \<in> it \<Longrightarrow> k' \<le> k \<rbrakk> \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
        and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
        and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> dom m; \<not> c \<sigma>; I it \<sigma>;
                  \<And>k k'. \<lbrakk>k \<in> it; k' \<in> (dom m)-it\<rbrakk> \<Longrightarrow> k \<le> k'\<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (it c f \<sigma>0)"
  using assms
  unfolding set_iterator_map_linord_def
  by (rule map_iterator_genord_rule_insert_P) auto

  lemma map_iterator_rev_linord_rule_P:
    assumes "map_iterator_rev_linord it m"
        and I0: "I (dom m) \<sigma>0"
        and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; m k = Some v; it \<subseteq> dom m; I it \<sigma>;
                 \<And>k'. k' \<in> it \<Longrightarrow> k' \<le> k; 
                 \<And>k'. k' \<in> (dom m)-it \<Longrightarrow> k \<le> k'\<rbrakk> \<Longrightarrow> I (it - {k}) (f (k, v) \<sigma>)"
        and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
        and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma>;
                  \<And>k k'. \<lbrakk>k \<in> (dom m)-it; k' \<in> it\<rbrakk> \<Longrightarrow> k' \<le> k\<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (it c f \<sigma>0)"
  using assms
  unfolding set_iterator_map_rev_linord_def
  by (rule map_iterator_genord_rule_P) auto

  lemma map_iterator_rev_linord_rule_insert_P:
    assumes "map_iterator_rev_linord it m"
        and I0: "I {} \<sigma>0"
        and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> dom m - it; m k = Some v; it \<subseteq> dom m; I it \<sigma>;
                 \<And>k'. k' \<in> (dom m - it) \<Longrightarrow> k' \<le> k; 
                 \<And>k'. k' \<in> it \<Longrightarrow> k \<le> k'\<rbrakk> \<Longrightarrow> I (insert k it) (f (k, v) \<sigma>)"
        and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
        and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> dom m; \<not> c \<sigma>; I it \<sigma>;
                  \<And>k k'. \<lbrakk>k \<in> it; k' \<in> (dom m)-it\<rbrakk> \<Longrightarrow> k' \<le> k\<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (it c f \<sigma>0)"
  using assms
  unfolding set_iterator_map_rev_linord_def
  by (rule map_iterator_genord_rule_insert_P) auto
end

subsection \<open>Conversions to foldli\<close>

lemma set_iterator_genord_foldli_conv :
  "set_iterator_genord iti S R \<longleftrightarrow>
   (\<exists>l0. distinct l0 \<and> S = set l0 \<and> sorted_wrt R l0 \<and> iti = foldli l0)"
unfolding set_iterator_genord_def by simp

lemma set_iterator_genord_I [intro] :
  "\<lbrakk>distinct l0; S = set l0; sorted_wrt R l0; iti = foldli l0\<rbrakk> \<Longrightarrow>
   set_iterator_genord iti S R" unfolding set_iterator_genord_foldli_conv
   by blast

lemma set_iterator_foldli_conv :
  "set_iterator iti S \<longleftrightarrow>
   (\<exists>l0. distinct l0 \<and> S = set l0 \<and> iti = foldli l0)"
unfolding set_iterator_def set_iterator_genord_def by simp

lemma set_iterator_I [intro] :
  "\<lbrakk>distinct l0; S = set l0; iti = foldli l0\<rbrakk> \<Longrightarrow>
   set_iterator iti S" 
   unfolding set_iterator_foldli_conv
   by blast

context linorder begin
  lemma set_iterator_linord_foldli_conv :
    "set_iterator_linord iti S \<longleftrightarrow>
     (\<exists>l0. distinct l0 \<and> S = set l0 \<and> sorted l0 \<and> iti = foldli l0)"
  unfolding set_iterator_linord_def set_iterator_genord_def by (simp add: sorted_sorted_wrt)

  lemma set_iterator_linord_I [intro] :
    "\<lbrakk>distinct l0; S = set l0; sorted l0; iti = foldli l0\<rbrakk> \<Longrightarrow>
     set_iterator_linord iti S" 
     unfolding set_iterator_linord_foldli_conv
     by blast

  lemma set_iterator_rev_linord_foldli_conv :
    "set_iterator_rev_linord iti S \<longleftrightarrow>
     (\<exists>l0. distinct l0 \<and> S = set l0 \<and> sorted (rev l0) \<and> iti = foldli l0)"
  unfolding set_iterator_rev_linord_def set_iterator_genord_def by simp

  lemma set_iterator_rev_linord_I [intro] :
    "\<lbrakk>distinct l0; S = set l0; sorted (rev l0); iti = foldli l0\<rbrakk> \<Longrightarrow>
     set_iterator_rev_linord iti S" 
     unfolding set_iterator_rev_linord_foldli_conv
     by blast
end


lemma map_iterator_genord_foldli_conv :
  "map_iterator_genord iti m R \<longleftrightarrow>
   (\<exists>(l0::('k \<times> 'v) list). distinct (map fst l0) \<and> m = map_of l0 \<and> sorted_wrt R l0 \<and> iti = foldli l0)"
proof -
  { fix l0 :: "('k \<times> 'v) list"
    assume dist: "distinct l0"
    have "(map_to_set m = set l0) \<longleftrightarrow>
          (distinct (map fst l0) \<and>
           m = map_of l0)"
    proof (cases "distinct (map fst l0)")
      case True thus ?thesis by (metis map_of_map_to_set)
    next
      case False note not_dist_fst = this

      with dist have "~(inj_on fst (set l0))" by (simp add: distinct_map)
      hence "set l0 \<noteq> map_to_set m"
        by (rule_tac notI) (simp add: map_to_set_def inj_on_def)
      with not_dist_fst show ?thesis by simp
    qed
  } 
  thus ?thesis
    unfolding set_iterator_genord_def distinct_map
    by metis
qed

lemma map_iterator_genord_I [intro] :
  "\<lbrakk>distinct (map fst l0); m = map_of l0; sorted_wrt R l0; iti = foldli l0\<rbrakk> \<Longrightarrow>
   map_iterator_genord iti m R" 
   unfolding map_iterator_genord_foldli_conv
   by blast

lemma map_iterator_foldli_conv :
  "map_iterator iti m \<longleftrightarrow>
   (\<exists>l0. distinct (map fst l0) \<and> m = map_of l0 \<and> iti = foldli l0)"
unfolding set_iterator_def map_iterator_genord_foldli_conv 
by simp

lemma map_iterator_I [intro] :
  "\<lbrakk>distinct (map fst l0); m = map_of l0; iti = foldli l0\<rbrakk> \<Longrightarrow>
   map_iterator iti m" 
   unfolding map_iterator_foldli_conv
   by blast

context linorder begin

  lemma sorted_wrt_keys_map_fst:
    "sorted_wrt (\<lambda>(k,_) (k',_). R k k') l = sorted_wrt R (map fst l)"
    by (induct l) auto

  lemma map_iterator_linord_foldli_conv :
    "map_iterator_linord iti m \<longleftrightarrow>
     (\<exists>l0. distinct (map fst l0) \<and> m = map_of l0 \<and> sorted (map fst l0) \<and> iti = foldli l0)"
  unfolding set_iterator_map_linord_def map_iterator_genord_foldli_conv
  by (simp add: sorted_wrt_keys_map_fst sorted_sorted_wrt)

  lemma map_iterator_linord_I [intro] :
    "\<lbrakk>distinct (map fst l0); m = map_of l0; sorted (map fst l0); iti = foldli l0\<rbrakk> \<Longrightarrow>
     map_iterator_linord iti m" 
     unfolding map_iterator_linord_foldli_conv
     by blast

  lemma map_iterator_rev_linord_foldli_conv :
    "map_iterator_rev_linord iti m \<longleftrightarrow>
     (\<exists>l0. distinct (map fst l0) \<and> m = map_of l0 \<and> sorted (rev (map fst l0)) \<and> iti = foldli l0)"
  unfolding set_iterator_map_rev_linord_def map_iterator_genord_foldli_conv 
  by (simp add: sorted_wrt_keys_map_fst)

  lemma map_iterator_rev_linord_I [intro] :
    "\<lbrakk>distinct (map fst l0); m = map_of l0; sorted (rev (map fst l0)); iti = foldli l0\<rbrakk> \<Longrightarrow>
     map_iterator_rev_linord iti m" 
     unfolding map_iterator_rev_linord_foldli_conv
     by blast

end

end
