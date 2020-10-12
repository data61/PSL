(*  Title:       Iterators over Representations of Finite Sets
    Author:      Thomas Tuerk <tuerk@in.tum.de>
    Maintainer:  Thomas Tuerk <tuerk@in.tum.de>
*)
section \<open>\isaheader{Iterators over Representations of Finite Sets}\<close>
theory SetAbstractionIterator
imports Main SetIterator 
begin

text \<open>Sometimes, an iterator does not iterate over an abstract set directly. 
 Especialy, if datastructures that are composed of several concrete datastructures 
 for maps or sets are involved, it might be interesting to iterate over 
 representations of values instead of the abstract values. This leads to the following construct.\<close> 

locale set_iterator_abs_genord =
  fixes \<alpha> :: "'xc \<Rightarrow> 'xa"
    and invar :: "'xc \<Rightarrow> bool"  
    and iti::"('xc,'\<sigma>) set_iterator"
    and S0::"'xa set" 
    and R::"'xa \<Rightarrow> 'xa \<Rightarrow> bool"
  assumes foldli_transform:
    "\<exists>lc. (\<forall>xc \<in> set lc. invar xc) \<and> 
          distinct (map \<alpha> lc) \<and> S0 = set (map \<alpha> lc) \<and> 
          sorted_wrt R (map \<alpha> lc) \<and> iti = foldli lc"
begin
  text \<open>In the simplest case, the function used for iteration does not depend on
    the representation, but just the abstract values. In this case, the \emph{normal} iterators
    can be used with an adapted function.\<close> 
  lemma remove_abs :
    assumes f_OK: "\<And>xc. invar xc \<Longrightarrow> \<alpha> xc \<in> S0 \<Longrightarrow> fc xc = fa (\<alpha> xc)"
        and it_OK: "\<And>iti. set_iterator_genord iti S0 R \<Longrightarrow> P (iti c fa \<sigma>0)"
    shows "P (iti c fc \<sigma>0)"
  proof -
    from foldli_transform obtain lc where 
          lc_invar: "\<And>xc. xc \<in> set lc \<Longrightarrow> invar xc" 
      and \<alpha>_props: "distinct (map \<alpha> lc)" "S0 = set (map \<alpha> lc)" 
                   "sorted_wrt R (map \<alpha> lc)" 
      and iti_eq: "iti = foldli lc" by blast

    from \<alpha>_props have "set_iterator_genord (foldli (map \<alpha> lc)) S0 R"
      by (rule_tac set_iterator_genord_I [of "map \<alpha> lc"]) simp_all
    with it_OK have P_OK: "P (foldli (map \<alpha> lc) c fa \<sigma>0)" by blast

    from lc_invar f_OK[unfolded \<alpha>_props(2)]
    have "foldli (map \<alpha> lc) c fa \<sigma>0 = foldli lc c fc \<sigma>0"
      by (induct lc arbitrary: \<sigma>0) simp_all
 
    with P_OK iti_eq show ?thesis by simp
  qed

  text \<open>In general, one needs the representation, though. Even in this case,
    the construct can be reduced to standard iterators.\<close>
  lemma remove_abs2 :
    "\<exists>S0'. set_iterator_genord iti S0' (\<lambda>x y. R (\<alpha> x) (\<alpha> y)) \<and>
           inj_on \<alpha> S0' \<and> \<alpha> ` S0' = S0 \<and> (\<forall>x \<in> S0'. invar x)"
  proof -
    from foldli_transform obtain lc where 
          lc_invar: "\<And>xc. xc \<in> set lc \<Longrightarrow> invar xc" 
      and \<alpha>_props: "distinct (map \<alpha> lc)" "S0 = set (map \<alpha> lc)" 
                   "sorted_wrt R (map \<alpha> lc)" 
      and iti_eq: "iti = foldli lc" by blast
    from \<alpha>_props have it': "set_iterator_genord iti (set lc) (\<lambda>x y. R (\<alpha> x) (\<alpha> y))"
      apply (rule_tac set_iterator_genord_I [of lc])  
      apply (simp_all add: distinct_map sorted_wrt_map iti_eq)
    done

    from \<alpha>_props show ?thesis
      apply (rule_tac exI[where x = "set lc"])
      apply (simp add: lc_invar distinct_map it')
    done
  qed

  text \<open>Let's now derive the inference rules for iterators over representations.\<close>

  lemma iteratei_abs_simple_rule_P:
  assumes f_OK: "\<And>xc. invar xc \<Longrightarrow> \<alpha> xc \<in> S0 \<Longrightarrow> f xc = f' (\<alpha> xc)"
  assumes pre :
      "I S0 \<sigma>0"
      "\<And>S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0; 
                 \<forall>y\<in>S - {x}. R x y; \<forall>y\<in>S0 - S. R y x\<rbrakk> 
                 \<Longrightarrow> I (S - {x}) (f' x \<sigma>)"
      "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      "\<And>\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> {}; \<not> c \<sigma>; I S \<sigma>;
               \<forall>x\<in>S. \<forall>y\<in>S0-S. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iti c f \<sigma>0)"
    apply (rule remove_abs[of f f' P c \<sigma>0])
    apply (simp add: f_OK)
    apply (erule set_iterator_genord.iteratei_rule_P [of _ S0 R I])
    apply (simp_all add: pre)
  done

  lemma iteratei_abs_simple_rule_insert_P:
  assumes f_OK: "\<And>xc. invar xc \<Longrightarrow> \<alpha> xc \<in> S0 \<Longrightarrow> f xc = f' (\<alpha> xc)"
  assumes pre :
      "I {} \<sigma>0"
      "\<And>S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; \<forall>y\<in>(S0 - S) - {x}. R x y;
                 \<forall>y\<in>S. R y x\<rbrakk> 
                  \<Longrightarrow> I (insert x S) (f' x \<sigma>)"
      "\<And>\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>"
      "\<And>\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> S0; 
              \<not> (c \<sigma>); I S \<sigma>; \<forall>x\<in>S0-S. \<forall>y\<in>S. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (iti c f \<sigma>0)"
    apply (rule remove_abs[of f f' P c \<sigma>0])
    apply (simp add: f_OK)
    apply (erule set_iterator_genord.iteratei_rule_insert_P [of _ S0 R I])
    apply (simp_all add: pre)
  done

  lemma iteratei_abs_rule_P:
  assumes pre :
      "I S0 \<sigma>0"
      "\<And>S \<sigma> x. \<lbrakk> c \<sigma>; invar x; \<alpha> x \<in> S; I S \<sigma>; S \<subseteq> S0; 
                 \<forall>y\<in>S - {\<alpha> x}. R (\<alpha> x) y; \<forall>y\<in>S0 - S. R y (\<alpha> x)\<rbrakk> 
                 \<Longrightarrow> I (S - {\<alpha> x}) (f x \<sigma>)"
      "\<And>\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      "\<And>\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> {}; \<not> c \<sigma>; I S \<sigma>;
               \<forall>x\<in>S. \<forall>y\<in>S0-S. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iti c f \<sigma>0)"
  proof -
    obtain S0' where S0'_props: "set_iterator_genord iti S0' (\<lambda>x y. R (\<alpha> x) (\<alpha> y))"
       "inj_on \<alpha> S0'" "S0 = \<alpha> ` S0'" "\<And>x. x \<in> S0' \<Longrightarrow> invar x" by (metis remove_abs2)
  
    show ?thesis
    proof (rule set_iterator_genord.iteratei_rule_P[OF S0'_props(1), of "\<lambda>S \<sigma>. I (\<alpha> ` S) \<sigma>" \<sigma>0 c], goal_cases)
      case 1
      thus ?case using S0'_props pre by simp   
    next
      case 3 thus ?case using S0'_props pre by simp   
    next
      case prems: (2 S \<sigma> x)

      from prems S0'_props have inv_x: "invar x" by blast
      from prems(4) have subs_alpha: "\<alpha> ` S \<subseteq> \<alpha> ` S0'" by auto
      from S0'_props prems(2,4)
      have diff_alpha: "\<alpha> ` S - {\<alpha> x} = \<alpha> ` (S - {x})" "\<alpha> ` S0' - \<alpha> ` S = \<alpha> ` (S0' - S)"
       by (auto simp add: inj_on_def subset_iff Ball_def)

      show ?case 
        using pre(2)[of \<sigma> x "\<alpha> ` S"] S0'_props(3)  
        by (simp add: inv_x prems subs_alpha diff_alpha)
    next
      case prems: (4 \<sigma> S)
      show ?case
        using pre(4)[of "\<alpha> ` S" \<sigma>] prems S0'_props
        by auto
    qed
  qed

  lemma iteratei_abs_rule_insert_P:
  assumes pre :
      "I {} \<sigma>0"
      "\<And>S \<sigma> x. \<lbrakk> c \<sigma>; invar x; \<alpha> x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0; 
                 \<forall>y\<in>(S0 - S) - {\<alpha> x}. R (\<alpha> x) y; \<forall>y\<in>S. R y (\<alpha> x)\<rbrakk> 
                 \<Longrightarrow> I (insert (\<alpha> x) S) (f x \<sigma>)"
      "\<And>\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>"
      "\<And>\<sigma> S. \<lbrakk> S \<subseteq> S0; S \<noteq> S0; \<not> c \<sigma>; I S \<sigma>;
               \<forall>x\<in>S0-S. \<forall>y\<in>S. R y x \<rbrakk> \<Longrightarrow> P \<sigma>"
    shows "P (iti c f \<sigma>0)"
  proof -
    obtain S0' where S0'_props: "set_iterator_genord iti S0' (\<lambda>x y. R (\<alpha> x) (\<alpha> y))"
       "inj_on \<alpha> S0'" "S0 = \<alpha> ` S0'" "\<And>x. x \<in> S0' \<Longrightarrow> invar x" by (metis remove_abs2)
  
    show ?thesis
    proof (rule set_iterator_genord.iteratei_rule_insert_P[OF S0'_props(1), of "\<lambda>S \<sigma>. I (\<alpha> ` S) \<sigma>" \<sigma>0 c], goal_cases)
      case 1
      thus ?case using S0'_props pre by simp   
    next
      case 3
      thus ?case using S0'_props pre by simp   
    next
      case prems: (2 S \<sigma> x)

      from prems S0'_props have inv_x: "invar x" by blast
      from prems(4) have subs_alpha: "\<alpha> ` S \<subseteq> \<alpha> ` S0'" by auto
      from S0'_props prems(2,4)
      have diff_alpha: "\<alpha> ` (S0' - S) - {\<alpha> x} = \<alpha> ` ((S0' - S) - {x})" "\<alpha> ` S0' - \<alpha> ` S = \<alpha> ` (S0' - S)"
       by (auto simp add: inj_on_def subset_iff Ball_def)
      
      show ?case 
        using pre(2)[of \<sigma> x "\<alpha> ` S"] prems S0'_props(3)  
        by (simp add: diff_alpha inv_x subs_alpha)
    next
      case prems: (4 \<sigma> S)

      from prems(1) have subs_alpha: "\<alpha> ` S \<subseteq> \<alpha> ` S0'" by auto

      from S0'_props prems
      have diff_alpha: "\<alpha> ` S0' - \<alpha> ` S = \<alpha> ` (S0' - S)"
       by (auto simp add: inj_on_def subset_iff Ball_def)

      from prems(1,2) S0'_props(2,3)
      have alpha_eq: "\<alpha> ` S \<noteq> \<alpha> ` S0'"
        apply (simp add: inj_on_def set_eq_iff image_iff Bex_def subset_iff)
        apply blast
      done

      show ?case
        using pre(4)[of "\<alpha> ` S" \<sigma>] S0'_props prems
        by (auto simp add: subs_alpha diff_alpha alpha_eq)
    qed
  qed
end

lemma set_iterator_abs_genord_trivial:
  "set_iterator_abs_genord id (\<lambda>_. True) = set_iterator_genord"
by (simp add: set_iterator_genord_def set_iterator_abs_genord_def fun_eq_iff)

lemma set_iterator_abs_genord_trivial_simp [simp] :
  assumes "\<forall>x. invar x"
      and "\<forall>x. \<alpha> x = x"
shows "set_iterator_abs_genord \<alpha> invar = set_iterator_genord"
proof -
  from assms have "invar = (\<lambda>_. True)" and "\<alpha> = id"
    by (simp_all add: fun_eq_iff)
  thus ?thesis by (simp add: set_iterator_abs_genord_trivial)
qed

subsection \<open>Introduce iterators over representations\<close>
lemma set_iterator_abs_genord_I2 :
  assumes it_OK: "set_iterator_genord iti S0 Rc"
      and R_OK: "\<And>xc1 xc2. \<lbrakk>invar xc1; invar xc2; Rc xc1 xc2\<rbrakk> \<Longrightarrow> Ra (\<alpha> xc1) (\<alpha> xc2)"
      and dist: "\<And>xc1 xc2. \<lbrakk>invar xc1; invar xc2; xc1 \<in> S0; xc2 \<in> S0; \<alpha> xc1 = \<alpha> xc2\<rbrakk> \<Longrightarrow> xc1 = xc2"
      and invar: "\<And>xc. xc \<in> S0 \<Longrightarrow> invar xc"
      and S0'_eq: "S0' = \<alpha> ` S0"
  shows "set_iterator_abs_genord \<alpha> invar iti S0' Ra"
  proof -
    from it_OK obtain l0 where dist_l0: "distinct l0" and 
          S0_eq: "S0 = set l0" and 
          sort_Rc: "sorted_wrt Rc l0"  and iti_eq: "iti = foldli l0" 
      unfolding set_iterator_genord_def by auto

    have "set l0 \<subseteq> S0" unfolding S0_eq by simp
    with dist_l0 sort_Rc 
    have map_props: "distinct (map \<alpha> l0) \<and> sorted_wrt Ra (map \<alpha> l0)"
    proof (induct l0) 
      case Nil thus ?case by simp
    next
      case (Cons x l0)
      hence "distinct l0" and "x \<notin> set l0" and "x \<in> S0" and "set l0 \<subseteq> S0" and
            "distinct (map \<alpha> l0)" "sorted_wrt Ra (map \<alpha> l0)" "\<And>x'. x' \<in> set l0 \<Longrightarrow> Rc x x'"
        by (simp_all)
      thus ?case using dist[of x] R_OK[of x] invar 
        apply (simp add: image_iff Ball_def subset_iff)
        apply metis
      done
    qed

    show ?thesis
      unfolding S0'_eq
      apply (rule set_iterator_abs_genord.intro)
      apply (rule_tac exI[where x = l0])
      apply (simp add: iti_eq map_props S0_eq Ball_def invar)
    done
  qed


subsection \<open>Map-Iterators\<close>

lemma map_to_set_cong: 
  "map_to_set m1 = map_to_set m2 \<longleftrightarrow> m1 = m2"
apply (simp add: set_eq_iff map_to_set_def)
apply (simp add: fun_eq_iff)
apply (metis not_Some_eq)
done


definition "map_iterator_abs_genord \<alpha> invar it m R \<equiv> 
set_iterator_abs_genord (\<lambda>(k,v). (k, \<alpha> v)) (\<lambda>(k,v). invar v) it (map_to_set m) R"

lemma map_iterator_abs_genord_I2 :
  assumes it_OK: "map_iterator_genord iti m R'"
      and invar: "\<And>k v. m k = Some v \<Longrightarrow> invar v"
      and R_OK: "\<And>k v k' v'. invar v \<Longrightarrow> invar v' \<Longrightarrow> R' (k, v) (k', v') \<Longrightarrow> R (k, \<alpha> v) (k', \<alpha> v')"
      and m'_eq: "m' = ((map_option \<alpha>) o m)"
  shows "map_iterator_abs_genord \<alpha> invar iti m' R"
proof -
  let ?\<alpha>' = "\<lambda>(k,v). (k, \<alpha> v)"
  let ?invar' = "\<lambda>(k,v). invar v"

  have \<alpha>_rewr: "?\<alpha>' ` (map_to_set m) = map_to_set ((map_option \<alpha>) o m)"
    by (auto simp add: map_to_set_def)
 
  note rule' = set_iterator_abs_genord_I2[OF it_OK[unfolded set_iterator_def], 
    of ?invar' R ?\<alpha>' "map_to_set (map_option \<alpha> \<circ> m)", unfolded \<alpha>_rewr map_iterator_abs_genord_def[symmetric]]

  show ?thesis
    unfolding m'_eq
    apply (rule rule')
    apply (auto simp add: map_to_set_def invar R_OK)
  done
qed

lemma map_iterator_abs_genord_remove_abs2 :
  assumes iti: "map_iterator_abs_genord \<alpha> invar iti m R"
  obtains m' where "map_iterator_genord iti m' (\<lambda>(k, v) (k', v'). R (k, \<alpha> v) (k', \<alpha> v'))"
       "(map_option \<alpha>) o m' = m" "\<And>k v. m' k = Some v \<Longrightarrow> invar v"
  proof -
    let ?\<alpha>' = "\<lambda>(k,v). (k, \<alpha> v)"
    let ?invar' = "\<lambda>(k,v). invar v"

    from set_iterator_abs_genord.foldli_transform [OF iti[unfolded map_iterator_abs_genord_def]]
    obtain lc where lc_invar: "\<And>k v. (k, v) \<in> set lc \<Longrightarrow> invar v" 
      and \<alpha>_props: "distinct (map ?\<alpha>' lc)" "map_to_set m = set (map ?\<alpha>' lc)" 
                   "sorted_wrt R (map ?\<alpha>' lc)" 
      and iti_eq: "iti = foldli lc" by blast

    from \<alpha>_props(2)[symmetric] have in_lc: "\<And>k v. (k, v) \<in> set lc \<Longrightarrow> m k = Some (\<alpha> v)" 
      by (auto simp add: set_eq_iff image_iff map_to_set_def Ball_def Bex_def)
    from \<alpha>_props(1) have inj_on_\<alpha>': "inj_on ?\<alpha>' (set lc)" by (simp add: distinct_map)

    from in_lc inj_on_\<alpha>'
    have inj_on_fst: "inj_on fst (set lc)"
      apply (simp add: inj_on_def Ball_def)
      apply (metis option.inject)
    done

    let ?m' = "map_of lc"

    from \<alpha>_props have it': "map_iterator_genord iti ?m' (\<lambda>x y. R (?\<alpha>' x) (?\<alpha>' y))"
      apply (rule_tac set_iterator_genord_I [of lc])  
      apply (simp_all add: distinct_map sorted_wrt_map iti_eq map_to_set_map_of inj_on_fst)
    done

    from inj_on_fst \<alpha>_props(1)
    have "distinct (map fst (map ?\<alpha>' lc))" 
      by (auto simp add: distinct_map inj_on_def Ball_def)
    hence "map_to_set m = map_to_set (map_of (map ?\<alpha>' lc))"
      by (simp add: \<alpha>_props map_to_set_map_of)
    hence m_eq: "map_option \<alpha> \<circ> map_of lc = m"
      by (simp add: map_of_map[symmetric] map_to_set_cong)

    from that[of ?m'] it' lc_invar \<alpha>_props(1) show ?thesis
      by (simp add: distinct_map split_def inj_on_fst ran_distinct m_eq)
  qed


lemma map_iterator_abs_genord_rule_P:
  assumes iti_OK: "map_iterator_abs_genord \<alpha> invar iti m R"
      and I0: "I (dom m) \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; invar v; m k = Some (\<alpha> v); it \<subseteq> dom m; I it \<sigma>; 
                             \<forall>k' v'. k' \<in> it-{k} \<and> invar v' \<and> m k' = Some (\<alpha> v') \<longrightarrow> R (k, \<alpha> v) (k', \<alpha> v');
                             \<forall>k' v'. k' \<notin> it \<and> invar v' \<and> m k' = Some (\<alpha> v') \<longrightarrow> R (k', \<alpha> v') (k, \<alpha> v)\<rbrakk> \<Longrightarrow> 
                            I (it - {k}) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma>;
                         \<forall>k v k' v'. k \<notin> it \<and> invar v \<and> m k = Some (\<alpha> v) \<and> 
                                     k' \<in> it \<and> invar v' \<and> m k' = Some (\<alpha> v') \<longrightarrow> 
                                     R (k, \<alpha> v) (k', \<alpha> v') \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (iti c f \<sigma>0)"
proof -
  let ?\<alpha>' = "\<lambda>(k,v). (k, \<alpha> v)"
  let ?invar' = "\<lambda>(k,v). invar v"

  from map_iterator_abs_genord_remove_abs2 [OF iti_OK]
  obtain m' where m'_props: "map_iterator_genord iti m' (\<lambda>x y. R (?\<alpha>' x) (?\<alpha>' y))"
     "m = map_option \<alpha> \<circ> m'" "\<And>k v. m' k = Some v \<Longrightarrow> invar v" 
     by (auto simp add: split_def) 

  have dom_m'_eq: "dom m' = dom m"
    unfolding m'_props by (simp add: dom_def)

  show ?thesis
  proof (rule map_iterator_genord_rule_P[OF m'_props(1), of I], goal_cases)
    case 1
    thus ?case using I0 by (simp add: dom_m'_eq)   
  next
    case 3
    thus ?case using IF by simp   
  next
    case prems: (2 k v S \<sigma>)
    from IP [of \<sigma> k S v] prems
    show ?case
      by (simp add: m'_props) metis
  next
    case prems: (4 \<sigma> S)
    show ?case
      using II[of S \<sigma>] prems
      by (simp add: m'_props) metis
  qed
qed


lemma map_iterator_abs_genord_rule_insert_P:
  assumes iti_OK: "map_iterator_abs_genord \<alpha> invar iti m R"
      and I0: "I {} \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> dom m - it; invar v; m k = Some (\<alpha> v); it \<subseteq> dom m; I it \<sigma>; 
                             \<forall>k' v'. k' \<in> (dom m - it)-{k} \<and> invar v' \<and> m k' = Some (\<alpha> v') \<longrightarrow> R (k, \<alpha> v) (k', \<alpha> v');
                             \<forall>k' v'. k' \<in> it \<and> invar v' \<and> m k' = Some (\<alpha> v') \<longrightarrow> R (k', \<alpha> v') (k, \<alpha> v)\<rbrakk> \<Longrightarrow> 
                            I (insert k it) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> dom m; \<not> c \<sigma>; I it \<sigma>;
                         \<forall>k v k' v'. k \<in> it \<and> invar v \<and> m k = Some (\<alpha> v) \<and> 
                                     k' \<notin> it \<and> invar v' \<and> m k' = Some (\<alpha> v') \<longrightarrow> 
                                     R (k, \<alpha> v) (k', \<alpha> v') \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (iti c f \<sigma>0)"
proof -
  let ?\<alpha>' = "\<lambda>(k,v). (k, \<alpha> v)"
  let ?invar' = "\<lambda>(k,v). invar v"

  from map_iterator_abs_genord_remove_abs2 [OF iti_OK]
  obtain m' where m'_props: "map_iterator_genord iti m' (\<lambda>x y. R (?\<alpha>' x) (?\<alpha>' y))"
     "m = map_option \<alpha> \<circ> m'" "\<And>k v. m' k = Some v \<Longrightarrow> invar v" 
     by (auto simp add: split_def) 

  have dom_m'_eq: "dom m' = dom m"
    unfolding m'_props by (simp add: dom_def)

  show ?thesis
  proof (rule map_iterator_genord_rule_insert_P[OF m'_props(1), of I], goal_cases)
    case 1
    thus ?case using I0 by simp   
  next
    case 3
    thus ?case using IF by (simp add: dom_m'_eq)   
  next
    case prems: (2 k v S \<sigma>)
    from IP [of \<sigma> k S v] prems
    show ?case 
      by (simp add: m'_props) metis
  next
    case prems: (4 \<sigma> S)
    show ?case
      using II[of S \<sigma>] prems
      by (simp add: m'_props) metis
  qed
qed


subsection \<open>Unsorted Iterators\<close>

definition "set_iterator_abs \<alpha> invar it S0 \<equiv> set_iterator_abs_genord \<alpha> invar it S0 (\<lambda>_ _. True)"

lemma set_iterator_abs_trivial:
  "set_iterator_abs id (\<lambda>_. True) = set_iterator"
by (simp add: set_iterator_def set_iterator_abs_def fun_eq_iff)

lemma set_iterator_abs_trivial_simp [simp]:
  assumes "\<forall>x. invar x"
      and "\<forall>x. \<alpha> x = x"
shows "set_iterator_abs \<alpha> invar = set_iterator"
proof -
  from assms have "invar = (\<lambda>_. True)" and "\<alpha> = id"
    by (simp_all add: fun_eq_iff)
  thus ?thesis by (simp add: set_iterator_abs_trivial)
qed

lemma set_iterator_abs_I2 :
  assumes it_OK: "set_iterator iti S0"
      and dist: "\<And>xc1 xc2. \<lbrakk>invar xc1; invar xc2; xc1 \<in> S0; xc2 \<in> S0; \<alpha> xc1 = \<alpha> xc2\<rbrakk> \<Longrightarrow> xc1 = xc2"
      and invar: "\<And>xc. xc \<in> S0 \<Longrightarrow> invar xc"
      and S0'_OK: "S0' = \<alpha> ` S0"
  shows "set_iterator_abs \<alpha> invar iti S0'"
unfolding set_iterator_abs_def S0'_OK
apply (rule set_iterator_abs_genord_I2[OF it_OK[unfolded set_iterator_def], of invar _ \<alpha>])
apply (simp_all add: dist invar)
done


lemma set_iterator_abs_simple_rule_P:
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   (\<And>xc. invar xc \<Longrightarrow> f xc = f' (\<alpha> xc));
   I S0 \<sigma>0;
   !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> \<Longrightarrow> I (S - {x}) (f' x \<sigma>);
   !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
   !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
unfolding set_iterator_abs_def
using set_iterator_abs_genord.iteratei_abs_simple_rule_P [of \<alpha> invar it S0 "\<lambda>_ _. True" f f' I \<sigma>0 c P]
by simp 

lemma set_iterator_abs_simple_no_cond_rule_P:
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   (\<And>xc. invar xc \<Longrightarrow> f xc = f' (\<alpha> xc));
   I S0 \<sigma>0;
   !!S \<sigma> x. \<lbrakk> x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> \<Longrightarrow> I (S - {x}) (f' x \<sigma>);
   !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it (\<lambda>_. True) f \<sigma>0)"
using set_iterator_abs_simple_rule_P[of \<alpha> invar it S0 f f' I \<sigma>0 "\<lambda>_. True" P]
by simp 

lemma set_iterator_abs_simple_rule_insert_P :
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   (\<And>xc. invar xc \<Longrightarrow> f xc = f' (\<alpha> xc));
   I {} \<sigma>0;
   !!S \<sigma> x. \<lbrakk> c \<sigma>; x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0 \<rbrakk>  \<Longrightarrow> I (insert x S) (f' x \<sigma>);
   !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
   !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
unfolding set_iterator_abs_def
using set_iterator_abs_genord.iteratei_abs_simple_rule_insert_P [of \<alpha> invar it S0 "\<lambda>_ _. True" f f' I \<sigma>0 c P]
by simp 

lemma set_iterator_abs_no_cond_simple_rule_insert_P :
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   (\<And>xc. invar xc \<Longrightarrow> f xc = f' (\<alpha> xc));
   I {} \<sigma>0;
   !!S \<sigma> x. \<lbrakk> x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0 \<rbrakk>  \<Longrightarrow> I (insert x S) (f' x \<sigma>);
   !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it (\<lambda>_. True) f \<sigma>0)"
using set_iterator_abs_simple_rule_insert_P[of \<alpha> invar it S0 f f' I \<sigma>0 "\<lambda>_. True" P]
by simp 


lemma set_iterator_abs_rule_P:
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   I S0 \<sigma>0;
   !!S \<sigma> x. \<lbrakk> c \<sigma>; invar x; \<alpha> x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> \<Longrightarrow> I (S - {\<alpha> x}) (f x \<sigma>);
   !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>;
   !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> {} \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
unfolding set_iterator_abs_def
using set_iterator_abs_genord.iteratei_abs_rule_P [of \<alpha> invar it S0 "\<lambda>_ _. True" I \<sigma>0 c f P]
by simp 

lemma set_iterator_abs_no_cond_rule_P:
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   I S0 \<sigma>0;
   !!S \<sigma> x. \<lbrakk> invar x; \<alpha> x \<in> S; I S \<sigma>; S \<subseteq> S0 \<rbrakk> \<Longrightarrow> I (S - {\<alpha> x}) (f x \<sigma>);
   !!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it (\<lambda>_. True) f \<sigma>0)"
using set_iterator_abs_rule_P[of \<alpha> invar it S0 I \<sigma>0 "\<lambda>_. True" f P]
by simp 

lemma set_iterator_abs_rule_insert_P :
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   I {} \<sigma>0;
   !!S \<sigma> x. \<lbrakk> c \<sigma>; invar x; \<alpha> x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0 \<rbrakk>  \<Longrightarrow> I (insert (\<alpha> x) S) (f x \<sigma>);
   !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>;
   !!\<sigma> S. S \<subseteq> S0 \<Longrightarrow> S \<noteq> S0 \<Longrightarrow> \<not> c \<sigma> \<Longrightarrow> I S \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it c f \<sigma>0)"
unfolding set_iterator_abs_def
using set_iterator_abs_genord.iteratei_abs_rule_insert_P [of \<alpha> invar it S0 "\<lambda>_ _. True" I \<sigma>0 c f P]
by simp 

lemma set_iterator_abs_no_cond_rule_insert_P :
"\<lbrakk> set_iterator_abs \<alpha> invar it S0;
   I {} \<sigma>0;
   !!S \<sigma> x. \<lbrakk> invar x; \<alpha> x \<in> S0 - S; I S \<sigma>; S \<subseteq> S0 \<rbrakk>  \<Longrightarrow> I (insert (\<alpha> x) S) (f x \<sigma>);
   !!\<sigma>. I S0 \<sigma> \<Longrightarrow> P \<sigma>
 \<rbrakk> \<Longrightarrow> P (it (\<lambda>_. True) f \<sigma>0)"
using set_iterator_abs_rule_insert_P[of \<alpha> invar it S0 I \<sigma>0 "\<lambda>_. True" f P]
by simp 


subsection \<open>Unsorted Map-Iterators\<close>

definition "map_iterator_abs \<alpha> invar it m \<equiv> map_iterator_abs_genord \<alpha> invar it m (\<lambda>_ _. True)"

lemma map_iterator_abs_trivial:
  "map_iterator_abs id (\<lambda>_. True) = map_iterator"
by (simp add: set_iterator_def map_iterator_abs_def map_iterator_abs_genord_def 
              set_iterator_abs_genord_def set_iterator_genord_def fun_eq_iff)

lemma map_iterator_abs_trivial_simp [simp] :
  assumes "\<forall>x. invar x"
      and "\<forall>x. \<alpha> x = x"
shows "map_iterator_abs \<alpha> invar = map_iterator"
proof -
  from assms have "invar = (\<lambda>_. True)" and "\<alpha> = id"
    by (simp_all add: fun_eq_iff)
  thus ?thesis by (simp add: map_iterator_abs_trivial)
qed


lemma map_iterator_abs_I2 :
  assumes it_OK: "map_iterator iti m"
      and invar: "\<And>k v. m k = Some v \<Longrightarrow> invar v"
      and m'_eq: "m' = map_option \<alpha> \<circ> m"
  shows "map_iterator_abs \<alpha> invar iti m'"
using assms
unfolding map_iterator_abs_def set_iterator_def
by (rule_tac map_iterator_abs_genord_I2 [OF it_OK[unfolded set_iterator_def]]) simp_all

lemma map_iterator_abs_rule_P:
  assumes iti_OK: "map_iterator_abs \<alpha> invar iti m"
      and I0: "I (dom m) \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> it; invar v; m k = Some (\<alpha> v); it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> 
                            I (it - {k}) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> {}; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (iti c f \<sigma>0)"
apply (rule map_iterator_abs_genord_rule_P [OF iti_OK[unfolded map_iterator_abs_def], of I])
apply (simp_all add: I0 IP IF II)
done

lemma map_iterator_abs_no_cond_rule_P:
  assumes iti_OK: "map_iterator_abs \<alpha> invar iti m"
      and I0: "I (dom m) \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> k \<in> it; invar v; m k = Some (\<alpha> v); it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> 
                            I (it - {k}) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I {} \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (iti (\<lambda>_. True) f \<sigma>0)"
apply (rule map_iterator_abs_rule_P [OF iti_OK, of I])
apply (simp_all add: I0 IP IF)
done

lemma map_iterator_abs_rule_insert_P:
  assumes iti_OK: "map_iterator_abs \<alpha> invar iti m"
      and I0: "I {} \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> c \<sigma>; k \<in> dom m - it; invar v; m k = Some (\<alpha> v); it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> 
                            I (insert k it) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
      and II: "!!\<sigma> it. \<lbrakk> it \<subseteq> dom m; it \<noteq> dom m; \<not> c \<sigma>; I it \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "P (iti c f \<sigma>0)"
apply (rule map_iterator_abs_genord_rule_insert_P [OF iti_OK[unfolded map_iterator_abs_def], of I])
apply (simp_all add: I0 IP IF II)
done

lemma map_iterator_abs_no_cond_rule_insert_P:
  assumes iti_OK: "map_iterator_abs \<alpha> invar iti m"
      and I0: "I {} \<sigma>0"
      and IP: "!!k v it \<sigma>. \<lbrakk> k \<in> dom m - it; invar v; m k = Some (\<alpha> v); it \<subseteq> dom m; I it \<sigma> \<rbrakk> \<Longrightarrow> 
                            I (insert k it) (f (k, v) \<sigma>)"
      and IF: "!!\<sigma>. I (dom m) \<sigma> \<Longrightarrow> P \<sigma>"
  shows "P (iti (\<lambda>_. True) f \<sigma>0)"
apply (rule map_iterator_abs_genord_rule_insert_P [OF iti_OK[unfolded map_iterator_abs_def], of I])
apply (simp_all add: I0 IP IF)
done

end


