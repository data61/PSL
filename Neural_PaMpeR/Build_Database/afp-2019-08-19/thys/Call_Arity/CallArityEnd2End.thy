theory CallArityEnd2End
imports ArityTransform CoCallAnalysisImpl
begin

locale CallArityEnd2End
begin
sublocale CoCallAnalysisImpl.

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

  have 1: "1 = inc\<cdot>0" apply (simp add: inc_def) apply transfer apply simp done
  
  have [simp]: "Aeta_expand 1 (App (Var f) g) = (Lam [z]. App (App (Var f) g) z)"
    apply (simp add: 1 del: exp_assn.eq_iff)
    apply (subst change_Lam_Variable[of z "fresh_var (App (Var f) g)"])
    apply (auto simp add: fresh_Pair fresh_at_base pure_fresh disj intro!: flip_fresh_fresh  elim!: fresh_var_eqE)
    done

  have [simp]: "Aeta_expand 1 e = (Lam [z]. App e z)"
    apply (simp add: 1 del: exp_assn.eq_iff)
    apply (subst change_Lam_Variable[of z "fresh_var e"])
    apply (auto simp add: fresh_Pair fresh_at_base pure_fresh disj fresh intro!: flip_fresh_fresh  elim!: fresh_var_eqE)
    done

  show ?thesis
    by (simp del: Let_eq_iff add: map_transform_Cons map_transform_Nil disj[symmetric])
qed

end
end
