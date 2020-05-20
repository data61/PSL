(*  Author: Tobias Nipkow, Dmitriy Traytel *)

section "Connection Between Derivatives and Partial Derivatives"

(*<*)
theory Deriv_PDeriv
imports Derivatives_Finite
begin
(*>*)

lemma pderiv_not_is_Zero_is_Plus[simp]: "\<forall>x \<in> pderiv a r. \<not> is_Zero x \<and> \<not> is_Plus x"
  by (induct r) auto

lemma finite_pderiv[simp]: "finite (pderiv a r)"
  by (induct r) auto

lemma PLUS_inject: "\<lbrakk>\<forall>x \<in> set xs \<union> set ys. \<not> is_Zero x \<and> \<not> is_Plus x; sorted xs; sorted ys\<rbrakk> \<Longrightarrow>
  (PLUS xs = PLUS ys) \<longleftrightarrow> xs = ys"
proof (induct xs arbitrary: ys rule: list_singleton_induct)
  case nil then show ?case by (induct ys rule: list_singleton_induct) auto
next
  case single then show ?case by (induct ys rule: list_singleton_induct) auto
next
  case cons then show ?case by (induct ys rule: list_singleton_induct) auto
qed

lemma sorted_list_of_set_inject: "\<lbrakk>finite R; finite S\<rbrakk> \<Longrightarrow>
  (sorted_list_of_set R = sorted_list_of_set S) \<longleftrightarrow> R = S"
proof (induct R arbitrary: S rule: finite_linorder_min_induct)
  case empty then show ?case
  proof (induct S rule: finite_linorder_min_induct)
    case (insert b S) then show ?case by simp (metis insort_not_Nil)
  qed simp
next
  case (insert a R) from this(4,1-3) show ?case
  proof (induct S rule: finite_linorder_min_induct)
    case (insert b S)
    show ?case
    proof
      assume "sorted_list_of_set (insert a R) = sorted_list_of_set (insert b S)"
      with insert(1,2,4,5) have "insort a (sorted_list_of_set R) = insort b (sorted_list_of_set S)"
        by (elim box_equals[OF _ sorted_list_of_set.insert sorted_list_of_set.insert]) auto
      with insert(2,5) have "a # sorted_list_of_set R = b # sorted_list_of_set S"
        apply (cases "sorted_list_of_set R" "sorted_list_of_set S" rule: list.exhaust[case_product list.exhaust])
        apply (auto split: if_splits simp add: not_le)
        using insort_not_Nil apply metis
        using insert.prems(1) set_sorted_list_of_set apply fastforce
        using insert.prems(1) set_sorted_list_of_set apply fastforce
        using insert.prems(1) set_sorted_list_of_set apply fastforce
        using insert.hyps(1) set_sorted_list_of_set apply fastforce
        using insert.hyps(1) set_sorted_list_of_set apply fastforce
        using insert.hyps(1) set_sorted_list_of_set apply fastforce
        using insert.hyps(1) set_sorted_list_of_set apply fastforce
        using insert.hyps(1) set_sorted_list_of_set apply fastforce
        done
      with insert show "insert a R = insert b S" by auto
    next
      assume "insert a R = insert b S"
      then show "sorted_list_of_set (insert a R) = sorted_list_of_set (insert b S)" by simp
    qed
  qed simp
qed

lemma flatten_PLUS_inject: "\<lbrakk>\<forall>x \<in> R \<union> S. \<not> is_Zero x \<and> \<not> is_Plus x; finite R; finite S\<rbrakk> \<Longrightarrow>
  (flatten PLUS R = flatten PLUS S) = (R = S)"
  by (rule trans[OF PLUS_inject sorted_list_of_set_inject]) auto

primrec pset where
  "pset Zero = {}"
| "pset One = {One}"
| "pset (Atom a) = {Atom a}"
| "pset (Plus r s) = pset r \<union> pset s"
| "pset (Times r s) = Timess (pset r) s"
| "pset (Star r) = {Star r}"

lemma pset_not_is_Zero_is_Plus[simp]: "\<forall>x \<in> pset r. \<not> is_Zero x \<and> \<not> is_Plus x"
  by (induct r) auto

lemma finite_pset[simp]: "finite (pset r)"
  by (induct r) auto

lemma pset_deriv: "pset (deriv a r) = pderiv a r"
  by (induct r) auto

definition pnorm where
  "pnorm = flatten PLUS o pset"

lemma pnorm_deriv_eq_iff_pderiv_eq:
  "pnorm (deriv a r) = pnorm (deriv a s) \<longleftrightarrow> pderiv a r = pderiv a s"
  unfolding pnorm_def o_apply pset_deriv
  by (rule flatten_PLUS_inject) auto

fun pnPlus :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
  "pnPlus Zero r = r"
| "pnPlus r Zero = r"
| "pnPlus (Plus r s) t = pnPlus r (pnPlus s t)"
| "pnPlus r (Plus s t) =
     (if r = s then (Plus s t)
     else if le_rexp r s then Plus r (Plus s t)
     else Plus s (pnPlus r t))"
| "pnPlus r s =
     (if r = s then r
      else if le_rexp r s then Plus r s
      else Plus s r)"

fun pnTimes :: "'a::linorder rexp \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp" where
  "pnTimes Zero r = Zero"
| "pnTimes (Plus r s) t = pnPlus (pnTimes r t) (pnTimes s t)"
| "pnTimes r s = Times r s"

primrec pnorm_alt :: "'a::linorder rexp \<Rightarrow> 'a rexp" where
  "pnorm_alt Zero = Zero"
| "pnorm_alt One = One"
| "pnorm_alt (Atom a) = Atom a"
| "pnorm_alt (Plus r s) = pnPlus (pnorm_alt r) (pnorm_alt s)"
| "pnorm_alt (Times r s) = pnTimes (pnorm_alt r) s"
| "pnorm_alt (Star r) = Star r"

lemma pset_pnPlus:
  "pset (pnPlus r s) = pset (Plus r s)"
  by (induct r s rule: pnPlus.induct) auto

lemma pset_pnTimes:
  "pset (pnTimes r s) = pset (Times r s)"
  by (induct r s rule: pnTimes.induct) (auto simp: pset_pnPlus)

lemma pset_pnorm_alt_Times: "s \<in> pset r \<Longrightarrow> pnTimes (pnorm_alt s) t = Times (pnorm_alt s) t"
  by (induct r arbitrary: s t) auto

lemma pset_pnorm_alt:
  "pset (pnorm_alt r) = pnorm_alt ` pset r"
  by (induct r) (auto simp: pset_pnPlus pset_pnTimes pset_pnorm_alt_Times image_iff)

lemma pset_pnTimes_Times: "s \<in> pset r \<Longrightarrow> pnTimes s t = Times s t"
  by (induct r arbitrary: s t) auto

lemma pset_pnorm_alt_id: "s \<in> pset r \<Longrightarrow> pnorm_alt s = s"
  by (induct r arbitrary: s) (auto simp: pset_pnTimes_Times)

lemma pnorm_alt_image_pset: "pnorm_alt ` pset r = pset r"
  by (induction r) (auto, auto simp add: pset_pnorm_alt_id pset_pnTimes_Times image_iff)

lemma pnorm_pnorm_alt: "pnorm (pnorm_alt r) = pnorm r"
  by (induct r) (auto simp: pnorm_def pset_pnPlus pset_pnTimes pset_pnorm_alt pnorm_alt_image_pset)

lemma pnPlus_singleton_PLUS: 
  "\<lbrakk>xs \<noteq> []; sorted xs; distinct xs; \<forall>x \<in> {x} \<union> set xs. \<not>is_Zero x \<and> \<not>is_Plus x\<rbrakk> \<Longrightarrow>
  pnPlus x (PLUS xs) = (if x \<in> set xs then PLUS xs else PLUS (insort x xs))"
proof (induct xs rule: list_singleton_induct)
  case (single y)
  thus ?case unfolding is_Zero_def is_Plus_def
    apply (cases x y rule: linorder_cases)
    apply (induct x y rule: pnPlus.induct)
    apply (auto simp: less_rexp_def less_eq_rexp_def)
    apply (cases y)
    apply auto
    apply (induct x y rule: pnPlus.induct)
    apply (auto simp: less_rexp_def less_eq_rexp_def)
    apply (induct x y rule: pnPlus.induct)
    apply (auto simp: less_rexp_def less_eq_rexp_def)
    done
next
  case (cons y1 y2 ys) thus ?case unfolding is_Zero_def is_Plus_def
    apply (cases x)
    apply (metis UnCI insertI1)
    apply simp apply (metis antisym less_eq_rexp_def)
    apply simp apply (metis antisym less_eq_rexp_def)
    apply (metis UnCI insertI1)
    apply simp apply (metis antisym less_eq_rexp_def)
    apply simp apply (metis antisym less_eq_rexp_def)
    done
qed simp

lemma pnPlus_PlusL[simp]: "t \<noteq> Zero \<Longrightarrow> pnPlus (Plus r s) t = pnPlus r (pnPlus s t)"
  by (induct t) auto

lemma pnPlus_ZeroR[simp]: "pnPlus r Zero = r"
  by (induct r) auto

lemma PLUS_eq_Zero: "PLUS xs = Zero \<longleftrightarrow> xs = [] \<or> xs = [Zero]"
  by (induct xs rule: list_singleton_induct) auto

lemma pnPlus_PLUS:
  "\<lbrakk>xs1 \<noteq> []; xs2 \<noteq> []; \<forall>x \<in> set (xs1 @ xs2). \<not>is_Zero x \<and> \<not>is_Plus x; sorted xs2; distinct xs2\<rbrakk>\<Longrightarrow>
  pnPlus (PLUS xs1) (PLUS xs2) = flatten PLUS (set (xs1 @ xs2))"
proof (induct xs1 arbitrary: xs2 rule: list_singleton_induct)
  case (single x1)
  thus ?case
    apply (auto intro!: trans[OF pnPlus_singleton_PLUS]
      simp: insert_absorb simp del: sorted_list_of_set_insert)
    apply (metis List.finite_set finite_sorted_distinct_unique sorted_list_of_set)
    apply (rule arg_cong[of _ _ PLUS])
    apply (metis remdups_id_iff_distinct sorted_list_of_set_sort_remdups sorted_sort_id)
    done
next
  case (cons x11 x12 xs1)
  then show ?case unfolding rexp_of_list.simps
  apply (subst pnPlus_PlusL)
  apply (unfold PLUS_eq_Zero) []
  apply (metis in_set_conv_decomp rexp.disc(1))
  apply (subst cons(1))
  apply (simp_all del: sorted_list_of_set_insert)
  apply (rule trans[OF pnPlus_singleton_PLUS])
  apply (simp_all add: sorted_insort set_insort_key del: sorted_list_of_set_insert)
  apply safe
  unfolding insert_commute[of x11]
  apply (auto simp only: Un_insert_left[of x11, symmetric] insert_absorb) []
  apply (auto simp only: Un_insert_right[of _ x11, symmetric] insert_absorb) []
  done
qed simp

lemma pnPlus_flatten_PLUS:
  "\<lbrakk>X1 \<noteq> {}; X2 \<noteq> {}; finite X1; finite X2; \<forall>x \<in> X1 \<union> X2.  \<not>is_Zero x \<and> \<not>is_Plus x\<rbrakk>\<Longrightarrow>
  pnPlus (flatten PLUS X1) (flatten PLUS X2) = flatten PLUS (X1 \<union> X2)"
  by (rule trans[OF pnPlus_PLUS]) auto

lemma pnPlus_pnorm: "pnPlus (pnorm r) (pnorm s) = pnorm (Plus r s)"
  by (cases "pset r = {} \<or> pset s = {}")
    (auto simp: pnorm_def pset_pnPlus pset_pnorm_alt intro: pnPlus_flatten_PLUS)

lemma pnTimes_not_Zero_or_Plus[simp]: "\<lbrakk>\<not> is_Zero x; \<not> is_Plus x\<rbrakk> \<Longrightarrow> pnTimes x r = Times x r"
  by (cases x) auto

lemma pnTimes_PLUS:
  "\<lbrakk>xs \<noteq> []; \<forall>x \<in> set xs. \<not>is_Zero x \<and> \<not>is_Plus x\<rbrakk>\<Longrightarrow>
  pnTimes (PLUS xs) r = flatten PLUS (Timess (set xs) r)"
proof (induct xs arbitrary: r rule: list_singleton_induct)
  case (cons x y xs) then show ?case unfolding rexp_of_list.simps pnTimes.simps
  apply (subst pnTimes_not_Zero_or_Plus)
  apply (simp_all add: sorted_insort set_insort_key del: sorted_list_of_set_insert)
  apply (subst pnPlus_singleton_PLUS)
  apply (simp_all add: sorted_insort set_insort_key del: sorted_list_of_set_insert)
  unfolding insert_commute[of "Times y r"]
  apply (simp del: sorted_list_of_set_insert)
  apply safe
  apply (subst insert_absorb[of "Times x r"])
  apply simp_all
  done
qed auto

lemma pnTimes_flatten_PLUS:
  "\<lbrakk>X1 \<noteq> {}; finite X1; \<forall>x \<in> X1. \<not>is_Zero x \<and> \<not>is_Plus x\<rbrakk>\<Longrightarrow>
  pnTimes (flatten PLUS X1) r = flatten PLUS (Timess X1 r)"
  by (rule trans[OF pnTimes_PLUS]) auto

lemma pnTimes_pnorm: "pnTimes (pnorm r1) r2 = pnorm (Times r1 r2)"
  by (cases "pset r1 = {}")
    (auto simp: pnorm_def pset_pnTimes pset_pnorm_alt intro: pnTimes_flatten_PLUS)

lemma pnorm_alt[symmetric]: "pnorm_alt r = pnorm r"
  by (induct r) (simp_all only: pnorm_alt.simps pnPlus_pnorm pnTimes_pnorm, auto simp: pnorm_def)

lemma insort_eq_Cons: "\<lbrakk>\<forall>a \<in> set xs. b < a; sorted xs\<rbrakk> \<Longrightarrow> insort b xs = b # xs"
  by (cases xs) auto

lemma pderiv_PLUS: "pderiv a (PLUS (x # xs)) = pderiv a x \<union> pderiv a (PLUS xs)"
  by (cases xs) auto

lemma pderiv_set_flatten_PLUS:
   "finite X \<Longrightarrow> pderiv (a :: 'a :: linorder) (flatten PLUS X) = pderiv_set a X"
proof (induction X rule: finite_linorder_min_induct)
  case (insert b X)
  then have "b \<notin> X" by auto
  then have "pderiv a (flatten PLUS (insert b X)) = pderiv a b \<union> pderiv a (flatten PLUS X)"
    by (simp add: pderiv_PLUS insort_eq_Cons insert.hyps)
  also from insert.IH have "\<dots> = pderiv a b \<union> pderiv_set a X" by simp
  finally show ?case by simp
qed simp

lemma fold_pderiv_set_flatten_PLUS:
  "\<lbrakk>w \<noteq> []; finite X\<rbrakk> \<Longrightarrow> fold pderiv_set w {flatten PLUS X} = fold pderiv_set w X"
  by (induct w arbitrary: X) (simp_all add: pderiv_set_flatten_PLUS)

lemma fold_pnorm_deriv:
  "fold (\<lambda>a r. pnorm (deriv a r)) w s = flatten PLUS (fold pderiv_set w {s})"
proof (induction w arbitrary: s)
  case (Cons x w) then show ?case
  proof (cases "w = []")
    case False
    show ?thesis using fold_pderiv_set_flatten_PLUS[OF False] Cons.IH
      by (auto simp: pnorm_def pset_deriv)
  qed (simp add: pnorm_def pset_deriv)
qed simp

primrec
  pnderiv :: "'a :: linorder \<Rightarrow> 'a rexp \<Rightarrow> 'a rexp"
where
  "pnderiv c (Zero) = Zero"
| "pnderiv c (One) = Zero"
| "pnderiv c (Atom c') = (if c = c' then One else Zero)"
| "pnderiv c (Plus r1 r2) = pnPlus (pnderiv c r1) (pnderiv c r2)"
| "pnderiv c (Times r1 r2) = 
    (if nullable r1 then pnPlus (pnTimes (pnderiv c r1) r2) (pnderiv c r2) else pnTimes (pnderiv c r1) r2)"
| "pnderiv c (Star r) = pnTimes (pnderiv c r) (Star r)"

lemma pnderiv_alt[code]: "pnderiv a r = pnorm (deriv a r)"
  by (induct r) (auto simp: pnorm_alt)

lemma pnderiv_pderiv: "pnderiv a r = flatten PLUS (pderiv a r)"
  unfolding pnderiv_alt pnorm_def o_apply pset_deriv ..

(*<*)
end
(*>*)
