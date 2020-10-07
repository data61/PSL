theory CallArityEnd2EndSafe
imports CallArityEnd2End CardArityTransformSafe CoCallImplSafe CoCallImplTTreeSafe TTreeImplCardinalitySafe
begin

locale CallArityEnd2EndSafe
begin
sublocale CoCallImplSafe.
sublocale CallArityEnd2End.

abbreviation transform_syn' ("\<T>\<^bsub>_\<^esub>") where "\<T>\<^bsub>a\<^esub> \<equiv> transform a"

lemma end2end:
  "c \<Rightarrow>\<^sup>* c' \<Longrightarrow>
  \<not> boring_step c' \<Longrightarrow>
  heap_upds_ok_conf c \<Longrightarrow>
  consistent (ae, ce, a, as, r) c \<Longrightarrow>
  \<exists>ae' ce' a' as' r'. consistent  (ae', ce', a', as', r') c' \<and> conf_transform  (ae, ce, a, as, r) c \<Rightarrow>\<^sub>G\<^sup>* conf_transform  (ae', ce', a', as', r') c'"
  by (rule card_arity_transform_safe)

theorem end2end_closed:
  assumes closed: "fv e = ({} :: var set)"
  assumes "([], e, []) \<Rightarrow>\<^sup>* (\<Gamma>,v,[])" and "isVal v"
  obtains \<Gamma>' and v'
  where "([], \<T>\<^bsub>0\<^esub> e, []) \<Rightarrow>\<^sup>* (\<Gamma>',v',[])" and "isVal v'"
    and "card (domA \<Gamma>') \<le> card (domA \<Gamma>)"
proof-
  note assms(2)
  moreover
  have "\<not> boring_step (\<Gamma>,v,[])" by (simp add: boring_step.simps)
  moreover
  have "heap_upds_ok_conf ([], e, [])" by simp
  moreover
  have "consistent (\<bottom>,\<bottom>,0,[],[]) ([], e, [])" using closed by (rule closed_consistent)
  ultimately
  obtain ae ce a as r where
    *: "consistent  (ae, ce, a, as, r) (\<Gamma>,v,[])" and
    **: "conf_transform  (\<bottom>, \<bottom>, 0, [], []) ([],e,[]) \<Rightarrow>\<^sub>G\<^sup>* conf_transform (ae, ce, a, as, r) (\<Gamma>,v,[])"
    by (metis end2end)

  let ?\<Gamma> = "map_transform Aeta_expand ae (map_transform transform ae (restrictA (-set r) \<Gamma>))"
  let ?v = "transform a v"

  from * have "set r \<subseteq> domA \<Gamma>" by auto

  have "conf_transform  (\<bottom>, \<bottom>, 0, [], []) ([],e,[]) = ([],transform 0 e,[])" by simp
  with **
  have "([], transform 0 e, []) \<Rightarrow>\<^sub>G\<^sup>* (?\<Gamma>, ?v, map Dummy (rev r))" by simp

  have "isVal ?v" using \<open>isVal v\<close> by simp

  have "fv (transform 0 e) = ({} :: var set)" using closed
    by (auto dest: subsetD[OF fv_transform])

  note sestoftUnGC'[OF \<open>([], transform 0 e, []) \<Rightarrow>\<^sub>G\<^sup>* (?\<Gamma>, ?v, map Dummy (rev r))\<close> \<open>isVal ?v\<close> \<open>fv (transform 0 e) = {}\<close>]
  then obtain \<Gamma>'
    where "([], transform 0 e, []) \<Rightarrow>\<^sup>* (\<Gamma>', ?v, [])"
    and "?\<Gamma> = restrictA (- set r) \<Gamma>'"
    and "set r \<subseteq> domA \<Gamma>'"
    by auto

  have "card (domA \<Gamma>) = card (domA ?\<Gamma> \<union> (set r \<inter> domA \<Gamma>))"
    by (rule arg_cong[where f = card]) auto
  also have "\<dots> = card (domA ?\<Gamma>) + card (set r \<inter> domA \<Gamma>)"
    by (rule card_Un_disjoint) auto
  also note \<open>?\<Gamma> = restrictA (- set r) \<Gamma>'\<close>
  also have "set r \<inter> domA \<Gamma> = set r \<inter> domA \<Gamma>'"
    using \<open>set r \<subseteq> domA \<Gamma>\<close>  \<open>set r \<subseteq> domA \<Gamma>'\<close> by auto
  also have "card (domA (restrictA (- set r) \<Gamma>')) + card (set r \<inter> domA \<Gamma>') = card (domA \<Gamma>')"
    by (subst card_Un_disjoint[symmetric]) (auto intro: arg_cong[where f = card])
  finally
  have "card (domA \<Gamma>') \<le> card (domA \<Gamma>)" by simp
  with \<open>([], transform 0 e, []) \<Rightarrow>\<^sup>* (\<Gamma>', ?v, [])\<close>  \<open>isVal ?v\<close>
  show thesis using that by blast
qed

lemma fresh_var_eqE[elim_format]: "fresh_var e = x \<Longrightarrow> x \<notin>  fv e"
  by (metis fresh_var_not_free)

lemma example1:
  fixes e :: exp
  fixes f g x y z :: var
  assumes Aexp_e: "\<And>a. Aexp e\<cdot>a = esing x\<cdot>(up\<cdot>a) \<squnion> esing y\<cdot>(up\<cdot>a)"
  assumes ccExp_e: "\<And>a. CCexp e\<cdot>a = \<bottom>"
  assumes [simp]: "transform 1 e = e"
  assumes "isVal e"
  assumes disj: "y \<noteq> f" "y \<noteq> g" "x \<noteq> y" "z \<noteq> f" "z \<noteq> g" "y \<noteq> x"
  assumes fresh: "atom z \<sharp> e"
  shows "transform 1 (let y be  App (Var f) g in (let x be e in (Var x))) = 
         let y be (Lam [z]. App (App (Var f) g) z) in (let x be (Lam [z]. App e z) in (Var x))"
proof-
  from arg_cong[where f = edom, OF Aexp_e]
  have "x \<in> fv e" by simp (metis Aexp_edom' insert_subset)
  hence [simp]: "\<not> nonrec [(x,e)]"
    by (simp add: nonrec_def)
 
  from \<open>isVal e\<close>
  have [simp]: "thunks [(x, e)] = {}"
    by (simp add: thunks_Cons)

  have [simp]: "CCfix [(x, e)]\<cdot>(esing x\<cdot>(up\<cdot>1) \<squnion> esing y\<cdot>(up\<cdot>1), \<bottom>) = \<bottom>"
    unfolding CCfix_def
    apply (simp add: fix_bottom_iff ccBindsExtra_simp)
    apply (simp add: ccBind_eq disj ccExp_e)
    done

  have [simp]: "Afix [(x, e)]\<cdot>(esing x\<cdot>(up\<cdot>1)) = esing x\<cdot>(up\<cdot>1) \<squnion> esing y\<cdot>(up\<cdot>1)"
    unfolding Afix_def
    apply simp
    apply (rule fix_eqI)
    apply (simp add: disj Aexp_e)
    apply (case_tac "z x")
    apply (auto simp add: disj Aexp_e)
    done

  have [simp]: "Aheap [(y, App (Var f) g)] (let x be e in Var x)\<cdot>1 = esing y\<cdot>((Aexp (let x be e in Var x )\<cdot>1) y)"
    by (auto simp add:  Aheap_nonrec_simp ABind_nonrec_eq pure_fresh fresh_at_base disj)

  have [simp]: "(Aexp (let x be e in Var x)\<cdot>1) = esing y\<cdot>(up\<cdot>1)"
    by (simp add: env_restr_join disj)
    
  have [simp]: "Aheap [(x, e)] (Var x)\<cdot>1 = esing x\<cdot>(up\<cdot>1)"
    by (simp add: env_restr_join disj)

  have [simp]: "Aeta_expand 1 (App (Var f) g) = (Lam [z]. App (App (Var f) g) z)"
    apply (simp add: one_is_inc_zero del: exp_assn.eq_iff)
    apply (subst change_Lam_Variable[of z "fresh_var (App (Var f) g)"])
    apply (auto simp add: fresh_Pair fresh_at_base pure_fresh disj intro!: flip_fresh_fresh  elim!: fresh_var_eqE)
    done

  have [simp]: "Aeta_expand 1 e = (Lam [z]. App e z)"
    apply (simp add: one_is_inc_zero del: exp_assn.eq_iff)
    apply (subst change_Lam_Variable[of z "fresh_var e"])
    apply (auto simp add: fresh_Pair fresh_at_base pure_fresh disj fresh intro!: flip_fresh_fresh  elim!: fresh_var_eqE)
    done

  show ?thesis
    by (simp del: Let_eq_iff add: map_transform_Cons disj[symmetric])
qed


end
end
