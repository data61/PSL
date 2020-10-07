theory "C-Meet"
imports C "HOLCF-Meet"
begin

instantiation C :: Finite_Meet_cpo begin
  fixrec C_meet :: "C \<rightarrow> C \<rightarrow> C"
    where "C_meet\<cdot>(C\<cdot>a)\<cdot>(C\<cdot>b) = C\<cdot>(C_meet\<cdot>a\<cdot>b)"
  
  lemma[simp]: "C_meet\<cdot>\<bottom>\<cdot>y = \<bottom>" "C_meet\<cdot>x\<cdot>\<bottom> = \<bottom>" by (fixrec_simp, cases x, fixrec_simp+)  

  instance
  apply standard
  proof(intro exI conjI strip)
    fix x y
    {
      fix t
      have "(t \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (t \<sqsubseteq> x \<and> t \<sqsubseteq> y)"
      proof (induct t rule:C.take_induct)
        fix n
        show "(C_take n\<cdot>t \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (C_take n\<cdot>t \<sqsubseteq> x \<and> C_take n\<cdot>t \<sqsubseteq> y)"
        proof (induct n arbitrary: t x y rule:nat_induct)
          case 0 thus ?case by auto
          next
          case (Suc n t x y)
            with C.nchotomy[of t] C.nchotomy[of x] C.nchotomy[of y]
            show ?case by fastforce
        qed
     qed auto
    } note * = this
    show "C_meet\<cdot>x\<cdot>y \<sqsubseteq> x" using * by auto
    show "C_meet\<cdot>x\<cdot>y \<sqsubseteq> y" using * by auto
    fix z
    assume "z \<sqsubseteq> x" and "z \<sqsubseteq> y"
    thus "z \<sqsubseteq> C_meet\<cdot>x\<cdot>y" using * by auto
qed
end

lemma C_meet_is_meet: "(z \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (z \<sqsubseteq> x \<and> z \<sqsubseteq> y)"
proof (induct z rule:C.take_induct)
  fix n
  show "(C_take n\<cdot>z \<sqsubseteq> C_meet\<cdot>x\<cdot>y) = (C_take n\<cdot>z \<sqsubseteq> x \<and> C_take n\<cdot>z \<sqsubseteq> y)"
  proof (induct n arbitrary: z x y rule:nat_induct)
    case 0 thus ?case by auto
    next
    case (Suc n z x y) thus ?case
      apply -
      apply (cases z, simp)
      apply (cases x, simp)
      apply (cases y, simp)
      apply (fastforce simp add: cfun_below_iff)
      done
  qed
qed auto

instance C :: cont_binary_meet
proof (standard, goal_cases)
  have [simp]:"\<And> x y. x \<sqinter> y = C_meet\<cdot>x\<cdot>y"
    using C_meet_is_meet
    by (blast intro: is_meetI)
  case 1 thus ?case
    by (simp add: ch2ch_Rep_cfunR contlub_cfun_arg contlub_cfun_fun)
qed

lemma [simp]: "C\<cdot>r \<sqinter> r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma [simp]: "r \<sqinter> C\<cdot>r = r"
  by (auto intro: is_meetI simp add: below_C)

lemma [simp]: "C\<cdot>r \<sqinter> C\<cdot>r' = C\<cdot>(r \<sqinter> r')"
  apply (rule is_meetI)
  apply (metis below_refl meet_below1 monofun_cfun_arg)
  apply (metis below_refl meet_below2 monofun_cfun_arg)
  apply (case_tac a)
  apply auto
  by (metis meet_above_iff)

end
