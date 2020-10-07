theory PreSimplyTyped
imports Fresh Permutation
begin

type_synonym tvar = nat

datatype type =
  TUnit
| TVar tvar
| TArr type type
| TPair type type

datatype 'a ptrm =
  PUnit
| PVar 'a
| PApp "'a ptrm" "'a ptrm"
| PFn 'a type "'a ptrm"
| PPair "'a ptrm" "'a ptrm"
| PFst "'a ptrm"
| PSnd "'a ptrm"

fun ptrm_fvs :: "'a ptrm \<Rightarrow> 'a set" where
  "ptrm_fvs PUnit = {}"
| "ptrm_fvs (PVar x) = {x}"
| "ptrm_fvs (PApp A B) = ptrm_fvs A \<union> ptrm_fvs B"
| "ptrm_fvs (PFn x _ A) = ptrm_fvs A - {x}"
| "ptrm_fvs (PPair A B) = ptrm_fvs A \<union> ptrm_fvs B"
| "ptrm_fvs (PFst P) = ptrm_fvs P"
| "ptrm_fvs (PSnd P) = ptrm_fvs P"

fun ptrm_apply_prm :: "'a prm \<Rightarrow> 'a ptrm \<Rightarrow> 'a ptrm" (infixr "\<bullet>" 150) where
  "ptrm_apply_prm \<pi> PUnit = PUnit"
| "ptrm_apply_prm \<pi> (PVar x) = PVar (\<pi> $ x)"
| "ptrm_apply_prm \<pi> (PApp A B) = PApp (ptrm_apply_prm \<pi> A) (ptrm_apply_prm \<pi> B)"
| "ptrm_apply_prm \<pi> (PFn x T A) = PFn (\<pi> $ x) T (ptrm_apply_prm \<pi> A)"
| "ptrm_apply_prm \<pi> (PPair A B) = PPair (ptrm_apply_prm \<pi> A) (ptrm_apply_prm \<pi> B)"
| "ptrm_apply_prm \<pi> (PFst P) = PFst (ptrm_apply_prm \<pi> P)"
| "ptrm_apply_prm \<pi> (PSnd P) = PSnd (ptrm_apply_prm \<pi> P)"

inductive ptrm_alpha_equiv :: "'a ptrm \<Rightarrow> 'a ptrm \<Rightarrow> bool" (infix "\<approx>" 100) where
  unit:       "PUnit \<approx> PUnit"
| var:        "(PVar x) \<approx> (PVar x)"
| app:        "\<lbrakk>A \<approx> B; C \<approx> D\<rbrakk> \<Longrightarrow> (PApp A C) \<approx> (PApp B D)"
| fn1:        "A \<approx> B \<Longrightarrow> (PFn x T A) \<approx> (PFn x T B)"
| fn2:        "\<lbrakk>a \<noteq> b; A \<approx> [a \<leftrightarrow> b] \<bullet> B; a \<notin> ptrm_fvs B\<rbrakk> \<Longrightarrow> (PFn a T A) \<approx> (PFn b T B)"
| pair:       "\<lbrakk>A \<approx> B; C \<approx> D\<rbrakk> \<Longrightarrow> (PPair A C) \<approx> (PPair B D)"
| fst:        "A \<approx> B \<Longrightarrow> PFst A \<approx> PFst B"
| snd:        "A \<approx> B \<Longrightarrow> PSnd A \<approx> PSnd B"

inductive_cases unitE: "PUnit \<approx> Y"
inductive_cases varE:  "PVar x \<approx> Y"
inductive_cases appE:  "PApp A B \<approx> Y"
inductive_cases fnE:   "PFn x T A \<approx> Y"
inductive_cases pairE: "PPair A B \<approx> Y"
inductive_cases fstE:  "PFst P \<approx> Y"
inductive_cases sndE:  "PSnd P \<approx> Y"

lemma ptrm_prm_apply_id:
  shows "\<epsilon> \<bullet> X = X"
by(induction X, simp_all add: prm_apply_id)

lemma ptrm_prm_apply_compose:
  shows "\<pi> \<bullet> \<sigma> \<bullet> X = (\<pi> \<diamondop> \<sigma>) \<bullet> X"
by(induction X, simp_all add: prm_apply_composition)

lemma ptrm_size_prm:
  shows "size X = size (\<pi> \<bullet> X)"
by(induction X, auto)

lemma ptrm_size_alpha_equiv:
  assumes "X \<approx> Y"
  shows "size X = size Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct)
  case (fn2 a b A B T)
    hence "size A = size B" using ptrm_size_prm by metis
    thus ?case by auto
  next
qed auto

lemma ptrm_fvs_finite:
  shows "finite (ptrm_fvs X)"
by(induction X, auto)

lemma ptrm_prm_fvs:
  shows "ptrm_fvs (\<pi> \<bullet> X) = \<pi> {$} ptrm_fvs X"
proof(induction X)
  case (PUnit)
    thus ?case unfolding prm_set_def by simp
  next
  case (PVar x)
    have "ptrm_fvs (\<pi> \<bullet> PVar x) = ptrm_fvs (PVar (\<pi> $ x))" by simp
    moreover have "... = {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PVar x)" by simp
    ultimately show ?case by metis
  next
  case (PApp A B)
    have "ptrm_fvs (\<pi> \<bullet> PApp A B) = ptrm_fvs (PApp (\<pi> \<bullet> A) (\<pi> \<bullet> B))" by simp
    moreover have "... = ptrm_fvs (\<pi> \<bullet> A) \<union> ptrm_fvs (\<pi> \<bullet> B)" by simp
    moreover have "... = \<pi> {$} ptrm_fvs A \<union> \<pi> {$} ptrm_fvs B" using PApp.IH by metis
    moreover have "... = \<pi> {$} (ptrm_fvs A \<union> ptrm_fvs B)" using prm_set_distributes_union by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PApp A B)" by simp
    ultimately show ?case by metis
  next
  case (PFn x T A)
    have "ptrm_fvs (\<pi> \<bullet> PFn x T A) = ptrm_fvs (PFn (\<pi> $ x) T (\<pi> \<bullet> A))" by simp
    moreover have "... = ptrm_fvs (\<pi> \<bullet> A) - {\<pi> $ x}" by simp
    moreover have "... = \<pi> {$} ptrm_fvs A - {\<pi> $ x}" using PFn.IH by metis
    moreover have "... = \<pi> {$} ptrm_fvs A - \<pi> {$} {x}" using prm_set_singleton by metis
    moreover have "... = \<pi> {$} (ptrm_fvs A - {x})" using prm_set_distributes_difference by metis
    moreover have "... = \<pi> {$} ptrm_fvs (PFn x T A)" by simp
    ultimately show ?case by metis
  next
  case (PPair A B)
    thus ?case
      using prm_set_distributes_union ptrm_apply_prm.simps(5) ptrm_fvs.simps(5)
      by fastforce
  next
  case (PFst P)
    thus ?case by auto
  next
  case (PSnd P)
    thus ?case by auto
  next
qed

lemma ptrm_alpha_equiv_fvs:
  assumes "X \<approx> Y"
  shows "ptrm_fvs X = ptrm_fvs Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct)
  case (fn2 a b A B T)
    have "ptrm_fvs (PFn a T A) = ptrm_fvs A - {a}" by simp
    moreover have "... = ptrm_fvs ([a \<leftrightarrow> b] \<bullet> B) - {a}" using fn2.IH by metis
    moreover have "... = ([a \<leftrightarrow> b] {$} ptrm_fvs B) - {a}" using ptrm_prm_fvs by metis
    moreover have "... = ptrm_fvs B - {b}"  proof -
      consider "b \<in> ptrm_fvs B" | "b \<notin> ptrm_fvs B" by auto
      thus ?thesis proof(cases)
        case 1
          have "[a \<leftrightarrow> b] {$} ptrm_fvs B - {a} = [b \<leftrightarrow> a] {$} ptrm_fvs B - {a}" using prm_unit_commutes by metis
          moreover have "... = ((ptrm_fvs B - {b}) \<union> {a}) - {a}"
            using prm_set_unit_action \<open>b \<in> ptrm_fvs B\<close> \<open>a \<notin> ptrm_fvs B\<close> by metis
          moreover have "... = ptrm_fvs B - {b}" using \<open>a \<notin> ptrm_fvs B\<close> \<open>a \<noteq> b\<close>
            using Diff_insert0 Diff_insert2 Un_insert_right insert_Diff1 insert_is_Un singletonI
              sup_bot.right_neutral by blast (* why?! *)
          ultimately show ?thesis by metis
        next
        case 2
          hence "[a \<leftrightarrow> b] {$} ptrm_fvs B - {a} = ptrm_fvs B - {a}"
            using prm_set_unit_inaction \<open>a \<notin> ptrm_fvs B\<close> by metis
          moreover have "... = ptrm_fvs B" using \<open>a \<notin> ptrm_fvs B\<close> by simp
          moreover have "... = ptrm_fvs B - {b}" using \<open>b \<notin> ptrm_fvs B\<close> by simp
          ultimately show ?thesis by metis
        next
      qed
    qed
    moreover have "... = ptrm_fvs (PFn b T B)" by simp
    ultimately show ?case by metis
  next
qed auto

lemma ptrm_alpha_equiv_prm:
  assumes "X \<approx> Y"
  shows "\<pi> \<bullet> X \<approx> \<pi> \<bullet> Y"
using assms proof(induction rule: ptrm_alpha_equiv.induct)
  case (unit)
    thus ?case using ptrm_alpha_equiv.unit by simp
  next
  case (var x)
    thus ?case using ptrm_alpha_equiv.var by simp
  next
  case (app A B C D)
    thus ?case using ptrm_alpha_equiv.app by simp
  next
  case (fn1 A B x T)
    thus ?case using ptrm_alpha_equiv.fn1 by simp
  next
  case (fn2 a b A B T)
    have "\<pi> $ a \<noteq> \<pi> $ b" using \<open>a \<noteq> b\<close> using prm_apply_unequal by metis
    moreover have "\<pi> $ a \<notin> ptrm_fvs (\<pi> \<bullet> B)" using \<open>a \<notin> ptrm_fvs B\<close>
      using imageE prm_apply_unequal prm_set_def ptrm_prm_fvs by (metis (no_types, lifting))
    moreover have "\<pi> \<bullet> A \<approx> [\<pi> $ a \<leftrightarrow> \<pi> $ b] \<bullet> \<pi> \<bullet> B"
      using fn2.IH prm_compose_push ptrm_prm_apply_compose by metis
    ultimately show ?case using ptrm_alpha_equiv.fn2 by simp
  next
  case (pair A B C D)
    thus ?case using ptrm_alpha_equiv.pair by simp
  next
  case (fst A B)
    thus ?case using ptrm_alpha_equiv.fst by simp
  next
  case (snd A B)
    thus ?case using ptrm_alpha_equiv.snd by simp
  next
qed

lemma ptrm_swp_transfer:
  shows "[a \<leftrightarrow> b] \<bullet> X \<approx> Y \<longleftrightarrow> X \<approx> [a \<leftrightarrow> b] \<bullet> Y"
proof -
  have 1: "[a \<leftrightarrow> b] \<bullet> X \<approx> Y \<Longrightarrow> X \<approx> [a \<leftrightarrow> b] \<bullet> Y"
  proof -
    assume "[a \<leftrightarrow> b] \<bullet> X \<approx> Y"
    hence "\<epsilon> \<bullet> X \<approx> [a \<leftrightarrow> b] \<bullet> Y"
      using ptrm_alpha_equiv_prm ptrm_prm_apply_compose prm_unit_involution by metis
    thus ?thesis using ptrm_prm_apply_id by metis
  qed
  have 2: "X \<approx> [a \<leftrightarrow> b] \<bullet> Y \<Longrightarrow> [a \<leftrightarrow> b] \<bullet> X \<approx> Y"
  proof -
    assume "X \<approx> [a \<leftrightarrow> b] \<bullet> Y"
    hence "[a \<leftrightarrow> b] \<bullet> X \<approx> \<epsilon> \<bullet> Y"
      using ptrm_alpha_equiv_prm ptrm_prm_apply_compose prm_unit_involution by metis
    thus ?thesis using ptrm_prm_apply_id by metis
  qed
  from 1 and 2 show "[a \<leftrightarrow> b] \<bullet> X \<approx> Y \<longleftrightarrow> X \<approx> [a \<leftrightarrow> b] \<bullet> Y" by blast
qed

lemma ptrm_alpha_equiv_fvs_transfer:
  assumes "A \<approx> [a \<leftrightarrow> b] \<bullet> B" and "a \<notin> ptrm_fvs B"
  shows "b \<notin> ptrm_fvs A"
proof -
  from \<open>A \<approx> [a \<leftrightarrow> b] \<bullet> B\<close> have "[a \<leftrightarrow> b] \<bullet> A \<approx> B" using ptrm_swp_transfer by metis
  hence "ptrm_fvs B = [a \<leftrightarrow> b] {$} ptrm_fvs A"
    using ptrm_alpha_equiv_fvs ptrm_prm_fvs by metis
  hence "a \<notin> [a \<leftrightarrow> b] {$} ptrm_fvs A" using \<open>a \<notin> ptrm_fvs B\<close> by metis
  hence "b \<notin> [a \<leftrightarrow> b] {$} ([a \<leftrightarrow> b] {$} ptrm_fvs A)"
    using prm_set_notmembership prm_unit_action by metis
  thus ?thesis using prm_set_apply_compose prm_unit_involution prm_set_id by metis
qed

lemma ptrm_prm_agreement_equiv:
  assumes "\<And>a. a \<in> ds \<pi> \<sigma> \<Longrightarrow> a \<notin> ptrm_fvs M"
  shows "\<pi> \<bullet> M \<approx> \<sigma> \<bullet> M"
using assms proof(induction M arbitrary: \<pi> \<sigma>)
  case (PUnit)
    thus ?case using ptrm_alpha_equiv.unit by simp
  next
  case (PVar x)
    consider "x \<in> ds \<pi> \<sigma>" | "x \<notin> ds \<pi> \<sigma>" by auto
    thus ?case proof(cases)
      case 1
        hence "x \<notin> ptrm_fvs (PVar x)" using PVar.prems by blast
        thus ?thesis by simp
      next
      case 2
        hence "\<pi> $ x = \<sigma> $ x" using prm_disagreement_ext by metis
        thus ?thesis using ptrm_alpha_equiv.var by simp
      next
    qed
  next
  case (PApp A B)
    hence "\<pi> \<bullet> A \<approx> \<sigma> \<bullet> A" and "\<pi> \<bullet> B \<approx> \<sigma> \<bullet> B" by auto
    thus ?case using ptrm_alpha_equiv.app by auto
  next
  case (PFn x T A)
    consider "x \<notin> ds \<pi> \<sigma>" | "x \<in> ds \<pi> \<sigma>" by auto
    thus ?case proof(cases)
      case 1
        hence *: "\<pi> $ x = \<sigma> $ x" using prm_disagreement_ext by metis
        have "\<And>a. a \<in> ds \<pi> \<sigma> \<Longrightarrow> a \<notin> ptrm_fvs A"
        proof -
          fix a
          assume "a \<in> ds \<pi> \<sigma>"
          hence "a \<notin> ptrm_fvs (PFn x T A)" using PFn.prems by metis
          hence "a = x \<or> a \<notin> ptrm_fvs A" by auto
          thus "a \<notin> ptrm_fvs A" using \<open>a \<in> ds \<pi> \<sigma>\<close> \<open>x \<notin> ds \<pi> \<sigma>\<close> by auto
        qed
        thus ?thesis using PFn.IH * ptrm_alpha_equiv.fn1 ptrm_apply_prm.simps(3) by fastforce
      next
      case 2
        hence "\<pi> $ x \<noteq> \<sigma> $ x" using prm_disagreement_def CollectD by fastforce
        moreover have "\<pi> $ x \<notin> ptrm_fvs (\<sigma> \<bullet> A)"
        proof -
          have "y \<in> (ptrm_fvs A) \<Longrightarrow> \<pi> $ x \<noteq> \<sigma> $ y" for y
            using PFn \<open>\<pi> $ x \<noteq> \<sigma> $ x\<close> prm_apply_unequal prm_disagreement_ext ptrm_fvs.simps(4)
            by (metis Diff_iff empty_iff insert_iff)
          hence "\<pi> $ x \<notin> \<sigma> {$} ptrm_fvs A" unfolding prm_set_def by auto
          thus ?thesis using ptrm_prm_fvs by metis
        qed
        moreover have "\<pi> \<bullet> A \<approx> [\<pi> $ x \<leftrightarrow> \<sigma> $ x] \<bullet> \<sigma> \<bullet> A"
        proof -
          have "\<And>a. a \<in> ds \<pi> ([\<pi> $ x \<leftrightarrow> \<sigma> $ x] \<diamondop> \<sigma>) \<Longrightarrow> a \<notin> ptrm_fvs A" proof -
            fix a
            assume *: "a \<in> ds \<pi> ([\<pi> $ x \<leftrightarrow> \<sigma> $ x] \<diamondop> \<sigma>)"
            hence "a \<noteq> x" using \<open>\<pi> $ x \<noteq> \<sigma> $ x\<close>
              using prm_apply_composition prm_disagreement_ext prm_unit_action prm_unit_commutes
              by metis
            hence "a \<in> ds \<pi> \<sigma>"
              using * prm_apply_composition prm_apply_unequal prm_disagreement_ext prm_unit_inaction
              by metis
            thus "a \<notin> ptrm_fvs A" using \<open>a \<noteq> x\<close> PFn.prems by auto
          qed
          thus ?thesis using PFn by (simp add: ptrm_prm_apply_compose)
        qed
        ultimately show ?thesis using ptrm_alpha_equiv.fn2 by simp
      next    
    qed
  next
  case (PPair A B)
    hence "\<pi> \<bullet> A \<approx> \<sigma> \<bullet> A" and "\<pi> \<bullet> B \<approx> \<sigma> \<bullet> B" by auto
    thus ?case using ptrm_alpha_equiv.pair by auto
  next
  case (PFst P)
    hence "\<pi> \<bullet> P \<approx> \<sigma> \<bullet> P" by auto
    thus ?case using ptrm_alpha_equiv.fst by auto
  next
  case (PSnd P)
    hence "\<pi> \<bullet> P \<approx> \<sigma> \<bullet> P" by auto
    thus ?case using ptrm_alpha_equiv.snd by auto
  next
qed

lemma ptrm_prm_unit_inaction:
  assumes "a \<notin> ptrm_fvs X" "b \<notin> ptrm_fvs X"
  shows "[a \<leftrightarrow> b] \<bullet> X \<approx> X"
proof -
  have "(\<And>x. x \<in> ds [a \<leftrightarrow> b] \<epsilon> \<Longrightarrow> x \<notin> ptrm_fvs X)"
  proof -
    fix x
    assume "x \<in> ds [a \<leftrightarrow> b] \<epsilon>"
    hence "[a \<leftrightarrow> b] $ x \<noteq> \<epsilon> $ x"
      unfolding prm_disagreement_def
      by auto
    hence "x = a \<or> x = b"
      using prm_apply_id prm_unit_inaction by metis
    thus "x \<notin> ptrm_fvs X" using assms by auto
  qed
  hence "[a \<leftrightarrow> b] \<bullet> X \<approx> \<epsilon> \<bullet> X"
    using ptrm_prm_agreement_equiv by metis
  thus ?thesis using ptrm_prm_apply_id by metis
qed

lemma ptrm_alpha_equiv_reflexive:
  shows "M \<approx> M"
by(induction M, auto simp add: ptrm_alpha_equiv.intros)

corollary ptrm_alpha_equiv_reflp:
  shows "reflp ptrm_alpha_equiv"
unfolding reflp_def using ptrm_alpha_equiv_reflexive by auto

lemma ptrm_alpha_equiv_symmetric:
  assumes "X \<approx> Y"
  shows "Y \<approx> X"
using assms proof(induction rule: ptrm_alpha_equiv.induct, auto simp add: ptrm_alpha_equiv.intros)
  case (fn2 a b A B T)
    have "b \<noteq> a" using \<open>a \<noteq> b\<close> by auto
    have "B \<approx> [b \<leftrightarrow> a] \<bullet> A" using \<open>[a \<leftrightarrow> b] \<bullet> B \<approx> A\<close>
      using ptrm_swp_transfer prm_unit_commutes by metis

    have "b \<notin> ptrm_fvs A" using \<open>a \<notin> ptrm_fvs B\<close> \<open>A \<approx> [a \<leftrightarrow> b] \<bullet> B\<close> \<open>a \<noteq> b\<close>
      using ptrm_alpha_equiv_fvs_transfer by metis

    show ?case using \<open>b \<noteq> a\<close> \<open>B \<approx> [b \<leftrightarrow> a] \<bullet> A\<close> \<open>b \<notin> ptrm_fvs A\<close>
      using ptrm_alpha_equiv.fn2 by metis
  next
qed

corollary ptrm_alpha_equiv_symp:
  shows "symp ptrm_alpha_equiv"
unfolding symp_def using ptrm_alpha_equiv_symmetric by auto

lemma ptrm_alpha_equiv_transitive:
  assumes "X \<approx> Y" and "Y \<approx> Z"
  shows "X \<approx> Z"
using assms proof(induction "size X" arbitrary: X Y Z rule: less_induct)
  fix X Y Z :: "'a ptrm"
  assume IH: "\<And>K Y Z :: 'a ptrm. size K < size X \<Longrightarrow> K \<approx> Y \<Longrightarrow> Y \<approx> Z \<Longrightarrow> K \<approx> Z"
  assume "X \<approx> Y" and "Y \<approx> Z"
  show "X \<approx> Z" proof(cases X)
    case (PUnit)
      hence "Y = PUnit" using \<open>X \<approx> Y\<close> unitE by metis
      hence "Z = PUnit" using \<open>Y \<approx> Z\<close> unitE by metis
      thus ?thesis using ptrm_alpha_equiv.unit \<open>X = PUnit\<close> by metis
    next
    case (PVar x)
      hence "PVar x \<approx> Y" using \<open>X \<approx> Y\<close> by auto
      hence "Y = PVar x" using varE by metis
      hence "PVar x \<approx> Z" using \<open>Y \<approx> Z\<close> by auto
      hence "Z = PVar x" using varE by metis
      thus ?thesis using ptrm_alpha_equiv.var \<open>X = PVar x\<close> by metis
    next
    case (PApp A B)
      obtain C D where "Y = PApp C D" and "A \<approx> C" and "B \<approx> D"
        using appE \<open>X = PApp A B\<close> \<open>X \<approx> Y\<close> by metis
      hence "PApp C D \<approx> Z" using \<open>Y \<approx> Z\<close> by simp
      from this obtain E F where "Z = PApp E F" and "C \<approx> E" and "D \<approx> F" using appE by metis

      have "size A < size X" and "size B < size X" using \<open>X = PApp A B\<close> by auto
      hence "A \<approx> E" and "B \<approx> F" using IH \<open>A \<approx> C\<close> \<open>C \<approx> E\<close> \<open>B \<approx> D\<close> \<open>D \<approx> F\<close> by auto
      thus ?thesis using \<open>X = PApp A B\<close> \<open>Z = PApp E F\<close> ptrm_alpha_equiv.app by metis
    next
    case (PFn x T A)
      from this have X: "X = PFn x T A".
      hence *: "size A < size X" by auto

      obtain y B where "Y = PFn y T B"
        and Y_cases: "(x = y \<and> A \<approx> B) \<or> (x \<noteq> y \<and> A \<approx> [x \<leftrightarrow> y] \<bullet> B \<and> x \<notin> ptrm_fvs B)"
        using fnE \<open>X \<approx> Y\<close> \<open>X = PFn x T A\<close> by metis
      obtain z C where Z: "Z = PFn z T C"
        and Z_cases: "(y = z \<and> B \<approx> C) \<or> (y \<noteq> z \<and> B \<approx> [y \<leftrightarrow> z] \<bullet> C \<and> y \<notin> ptrm_fvs C)"
        using fnE \<open>Y \<approx> Z\<close> \<open>Y = PFn y T B\<close> by metis

      consider
        "x = y" "A \<approx> B" and "y = z" "B \<approx> C"
      | "x = y" "A \<approx> B" and "y \<noteq> z" "B \<approx> [y \<leftrightarrow> z] \<bullet> C" "y \<notin> ptrm_fvs C"
      | "x \<noteq> y" "A \<approx> [x \<leftrightarrow> y] \<bullet> B" "x \<notin> ptrm_fvs B" and "y = z" "B \<approx> C"
      | "x \<noteq> y" "A \<approx> [x \<leftrightarrow> y] \<bullet> B" "x \<notin> ptrm_fvs B" and "y \<noteq> z" "B \<approx> [y \<leftrightarrow> z] \<bullet> C" "y \<notin> ptrm_fvs C" and "x = z"
      | "x \<noteq> y" "A \<approx> [x \<leftrightarrow> y] \<bullet> B" "x \<notin> ptrm_fvs B" and "y \<noteq> z" "B \<approx> [y \<leftrightarrow> z] \<bullet> C" "y \<notin> ptrm_fvs C" and "x \<noteq> z"
        using Y_cases Z_cases by auto

      thus ?thesis proof(cases)
        case 1
          have "A \<approx> C" using \<open>A \<approx> B\<close> \<open>B \<approx> C\<close> IH * by metis
          have "x = z" using \<open>x = y\<close> \<open>y = z\<close> by metis
          show ?thesis using \<open>A \<approx> C\<close> \<open>x = z\<close> X Z
            using ptrm_alpha_equiv.fn1 by metis
        next
        case 2
          have "x \<noteq> z" using \<open>x = y\<close> \<open>y \<noteq> z\<close> by metis
          have "A \<approx> [x \<leftrightarrow> z] \<bullet> C" using \<open>A \<approx> B\<close> \<open>B \<approx> [y \<leftrightarrow> z] \<bullet> C\<close> \<open>x = y\<close> IH * by metis
          have "x \<notin> ptrm_fvs C" using \<open>x = y\<close> \<open>y \<notin> ptrm_fvs C\<close> by metis
          thus ?thesis using \<open>x \<noteq> z\<close> \<open>A \<approx> [x \<leftrightarrow> z] \<bullet> C\<close> \<open>x \<notin> ptrm_fvs C\<close> X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
        case 3
          have "x \<noteq> z" using \<open>x \<noteq> y\<close> \<open>y = z\<close> by metis
          have "[x \<leftrightarrow> y] \<bullet> B \<approx> [x \<leftrightarrow> y] \<bullet> C" using \<open>B \<approx> C\<close> ptrm_alpha_equiv_prm by metis
          have "A \<approx> [x \<leftrightarrow> z] \<bullet> C"
            using \<open>A \<approx> [x \<leftrightarrow> y] \<bullet> B\<close> \<open>[x \<leftrightarrow> y] \<bullet> B \<approx> [x \<leftrightarrow> y] \<bullet> C\<close> \<open>y = z\<close> IH *
            by metis
          have "x \<notin> ptrm_fvs C" using \<open>B \<approx> C\<close> \<open>x \<notin> ptrm_fvs B\<close> ptrm_alpha_equiv_fvs by metis
          thus ?thesis using \<open>x \<noteq> z\<close> \<open>A \<approx> [x \<leftrightarrow> z] \<bullet> C\<close> \<open>x \<notin> ptrm_fvs C\<close> X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
        case 4
          have "[x \<leftrightarrow> y] \<bullet> B \<approx> [x \<leftrightarrow> y] \<bullet> [y \<leftrightarrow> z] \<bullet> C"
            using \<open>B \<approx> [y \<leftrightarrow> z] \<bullet> C\<close> ptrm_alpha_equiv_prm by metis
          hence "A \<approx> [x \<leftrightarrow> y] \<bullet> [y \<leftrightarrow> z] \<bullet> C"
            using \<open>A \<approx> [x \<leftrightarrow> y] \<bullet> B\<close> IH * by metis
          hence "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C" using ptrm_prm_apply_compose by metis
          hence "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> x]) \<bullet> C" using \<open>x = z\<close> by metis
          hence "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [x \<leftrightarrow> y]) \<bullet> C" using prm_unit_commutes by metis
          hence "A \<approx> \<epsilon> \<bullet> C" using \<open>x = z\<close> prm_unit_involution by metis
          hence "A \<approx> C" using ptrm_prm_apply_id by metis

          thus ?thesis using \<open>x = z\<close> \<open>A \<approx> C\<close> X Z
            using ptrm_alpha_equiv.fn1 by metis
        next
        case 5
          have "x \<notin> ptrm_fvs C" proof -
            have "ptrm_fvs B = ptrm_fvs ([y \<leftrightarrow> z] \<bullet> C)"
              using ptrm_alpha_equiv_fvs \<open>B \<approx> [y \<leftrightarrow> z] \<bullet> C\<close> by metis
            hence "x \<notin> ptrm_fvs ([y \<leftrightarrow> z] \<bullet> C)" using \<open>x \<notin> ptrm_fvs B\<close> by auto
            hence "x \<notin> [y \<leftrightarrow> z] {$} ptrm_fvs C" using ptrm_prm_fvs by metis
            consider "z \<in> ptrm_fvs C" | "z \<notin> ptrm_fvs C" by auto
            thus ?thesis proof(cases)
              case 1
                hence "[y \<leftrightarrow> z] {$} ptrm_fvs C = ptrm_fvs C - {z} \<union> {y}"
                  using prm_set_unit_action prm_unit_commutes
                  and \<open>z \<in> ptrm_fvs C\<close> \<open>y \<notin> ptrm_fvs C\<close> by metis
                hence "x \<notin> ptrm_fvs C - {z} \<union> {y}" using \<open>x \<notin> [y \<leftrightarrow> z] {$} ptrm_fvs C\<close> by auto
                hence "x \<notin> ptrm_fvs C - {z}" using \<open>x \<noteq> y\<close> by auto
                thus ?thesis using \<open>x \<noteq> z\<close> by auto
              next
              case 2
                hence "[y \<leftrightarrow> z] {$} ptrm_fvs C = ptrm_fvs C" using prm_set_unit_inaction \<open>y \<notin> ptrm_fvs C\<close> by metis
                thus ?thesis using \<open>x \<notin> [y \<leftrightarrow> z] {$} ptrm_fvs C\<close> by auto
              next
            qed
          qed

          have "A \<approx> [x \<leftrightarrow> z] \<bullet> C" proof -
            have "A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C"
              using IH * \<open>A \<approx> [x \<leftrightarrow> y] \<bullet> B\<close> \<open>B \<approx> [y \<leftrightarrow> z] \<bullet> C\<close>
              and ptrm_alpha_equiv_prm ptrm_prm_apply_compose by metis

            have "([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C \<approx> [x \<leftrightarrow> z] \<bullet> C" proof -
              have "ds ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] = {x, y}"
                using \<open>x \<noteq> y\<close> \<open>y \<noteq> z\<close> \<open>x \<noteq> z\<close> prm_disagreement_composition by metis

              hence "\<And>a. a \<in> ds ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) [x \<leftrightarrow> z] \<Longrightarrow> a \<notin> ptrm_fvs C"
                using \<open>x \<notin> ptrm_fvs C\<close> \<open>y \<notin> ptrm_fvs C\<close>
                using Diff_iff Diff_insert_absorb insert_iff by auto
              thus ?thesis using ptrm_prm_agreement_equiv by metis
            qed

            thus ?thesis using IH *
              using \<open>A \<approx> ([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C\<close> \<open>([x \<leftrightarrow> y] \<diamondop> [y \<leftrightarrow> z]) \<bullet> C \<approx> [x \<leftrightarrow> z] \<bullet> C\<close>
              by metis
          qed

          show ?thesis using \<open>x \<noteq> z\<close> \<open>A \<approx> [x \<leftrightarrow> z] \<bullet> C\<close> \<open>x \<notin> ptrm_fvs C\<close> X Z
            using ptrm_alpha_equiv.fn2 by metis
        next
      qed
    next
    case (PPair A B)
      obtain C D where "Y = PPair C D" and "A \<approx> C" and "B \<approx> D"
        using pairE \<open>X = PPair A B\<close> \<open>X \<approx> Y\<close> by metis
      hence "PPair C D \<approx> Z" using \<open>Y \<approx> Z\<close> by simp
      from this obtain E F where "Z = PPair E F" and "C \<approx> E" and "D \<approx> F" using pairE by metis

      have "size A < size X" and "size B < size X" using \<open>X = PPair A B\<close> by auto
      hence "A \<approx> E" and "B \<approx> F" using IH \<open>A \<approx> C\<close> \<open>C \<approx> E\<close> \<open>B \<approx> D\<close> \<open>D \<approx> F\<close> by auto
      thus ?thesis using \<open>X = PPair A B\<close> \<open>Z = PPair E F\<close> ptrm_alpha_equiv.pair by metis
    next
    case (PFst P)
      obtain Q where "Y = PFst Q" "P \<approx> Q" using fstE \<open>X = PFst P\<close> \<open>X \<approx> Y\<close> by metis
      obtain R where "Z = PFst R" "Q \<approx> R" using fstE \<open>Y = PFst Q\<close> \<open>Y \<approx> Z\<close> by metis

      have "size P < size X" using \<open>X = PFst P\<close> by auto
      hence "P \<approx> R" using IH \<open>P \<approx> Q\<close> \<open>Q \<approx> R\<close> by metis
      thus ?thesis using \<open>X = PFst P\<close> \<open>Z = PFst R\<close> ptrm_alpha_equiv.fst by metis
    next
    case (PSnd P)
      obtain Q where "Y = PSnd Q" "P \<approx> Q" using sndE \<open>X = PSnd P\<close> \<open>X \<approx> Y\<close> by metis
      obtain R where "Z = PSnd R" "Q \<approx> R" using sndE \<open>Y = PSnd Q\<close> \<open>Y \<approx> Z\<close> by metis

      have "size P < size X" using \<open>X = PSnd P\<close> by auto
      hence "P \<approx> R" using IH \<open>P \<approx> Q\<close> \<open>Q \<approx> R\<close> by metis
      thus ?thesis using \<open>X = PSnd P\<close> \<open>Z = PSnd R\<close> ptrm_alpha_equiv.snd by metis
    next
  qed
qed

corollary ptrm_alpha_equiv_transp:
  shows "transp ptrm_alpha_equiv"
unfolding transp_def using ptrm_alpha_equiv_transitive by auto


type_synonym 'a typing_ctx = "'a \<rightharpoonup> type"

fun ptrm_infer_type :: "'a typing_ctx \<Rightarrow> 'a ptrm \<Rightarrow> type option" where
  "ptrm_infer_type \<Gamma> PUnit = Some TUnit"
| "ptrm_infer_type \<Gamma> (PVar x) = \<Gamma> x"
| "ptrm_infer_type \<Gamma> (PApp A B) = (case (ptrm_infer_type \<Gamma> A, ptrm_infer_type \<Gamma> B) of
     (Some (TArr \<tau> \<sigma>), Some \<tau>') \<Rightarrow> (if \<tau> = \<tau>' then Some \<sigma> else None)
   | _ \<Rightarrow> None
   )"
| "ptrm_infer_type \<Gamma> (PFn x \<tau> A) = (case ptrm_infer_type (\<Gamma>(x \<mapsto> \<tau>)) A of
     Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>)
   | None \<Rightarrow> None
   )"
| "ptrm_infer_type \<Gamma> (PPair A B) = (case (ptrm_infer_type \<Gamma> A, ptrm_infer_type \<Gamma> B) of
     (Some \<tau>, Some \<sigma>) \<Rightarrow> Some (TPair \<tau> \<sigma>)
   | _ \<Rightarrow> None
   )"
| "ptrm_infer_type \<Gamma> (PFst P) = (case ptrm_infer_type \<Gamma> P of
     (Some (TPair \<tau> \<sigma>)) \<Rightarrow> Some \<tau>
   | _ \<Rightarrow> None
   )"
| "ptrm_infer_type \<Gamma> (PSnd P) = (case ptrm_infer_type \<Gamma> P of
     (Some (TPair \<tau> \<sigma>)) \<Rightarrow> Some \<sigma>
   | _ \<Rightarrow> None
   )"

lemma ptrm_infer_type_swp_types:
  assumes "a \<noteq> b"
  shows "ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) X = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> X)"
using assms proof(induction X arbitrary: T S \<Gamma>)
  case (PUnit)
    thus ?case by simp
  next
  case (PVar x)
    consider "x = a" | "x = b" | "x \<noteq> a \<and> x \<noteq> b" by auto
    thus ?case proof(cases)
      assume "x = a"
      thus ?thesis using \<open>a \<noteq> b\<close> by (simp add: prm_unit_action)
      next

      assume "x = b"
      thus ?thesis using \<open>a \<noteq> b\<close>
        using prm_unit_action prm_unit_commutes fun_upd_same fun_upd_twist
        by (metis ptrm_apply_prm.simps(2) ptrm_infer_type.simps(2))
      next

      assume "x \<noteq> a \<and> x \<noteq> b"
      thus ?thesis by (simp add: prm_unit_inaction)
      next
    qed
  next
  case (PApp A B)
    thus ?case by simp
  next
  case (PFn x \<tau> A)
    hence *:
      "ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) A = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> A)"
      for T S \<Gamma>
      by metis

    consider "x = a" | "x = b" | "x \<noteq> a \<and> x \<noteq> b" by auto
    thus ?case proof(cases)
      case 1
        hence
          "ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> PFn x \<tau> A)
         = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) (PFn b \<tau> ([a \<leftrightarrow> b] \<bullet> A))"
          using prm_unit_action ptrm_apply_prm.simps(4) by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          by simp
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>, b \<mapsto> S)) A of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using * by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(b \<mapsto> S, a \<mapsto> T, a \<mapsto> \<tau>)) A of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using \<open>a \<noteq> b\<close> fun_upd_twist fun_upd_upd by metis
        moreover have "... = ptrm_infer_type (\<Gamma>(b \<mapsto> S, a \<mapsto> T)) (PFn x \<tau> A)"
          using \<open>x = a\<close> by simp
        moreover have "... = ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) (PFn x \<tau> A)"
          using \<open>a \<noteq> b\<close> fun_upd_twist by metis
        ultimately show ?thesis by metis
      next
      case 2
        hence
          "ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> PFn x \<tau> A)
         = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) (PFn a \<tau> ([a \<leftrightarrow> b] \<bullet> A))"
          using prm_unit_action prm_unit_commutes ptrm_apply_prm.simps(4) by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)(a \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          by simp
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using fun_upd_upd fun_upd_twist \<open>a \<noteq> b\<close> by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> \<tau>)) A of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using * by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)(b \<mapsto> \<tau>)) A of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using \<open>a \<noteq> b\<close> fun_upd_upd by metis
        moreover have "... = ptrm_infer_type (\<Gamma>(b \<mapsto> S, a \<mapsto> T)) (PFn x \<tau> A)"
          using \<open>x = b\<close> by simp
        moreover have "... = ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) (PFn x \<tau> A)"
          using \<open>a \<noteq> b\<close> fun_upd_twist by metis
        ultimately show ?thesis by metis
      next
      case 3
        hence "x \<noteq> a" "x \<noteq> b" by auto
        hence
          "ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> PFn x \<tau> A)
         = ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)) (PFn x \<tau> ([a \<leftrightarrow> b] \<bullet> A))"
          by (simp add: prm_unit_inaction)
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> S, b \<mapsto> T)(x \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          by simp
        moreover have "... = (case ptrm_infer_type (\<Gamma>(x \<mapsto> \<tau>, a \<mapsto> S, b \<mapsto> T)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> fun_upd_twist by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(x \<mapsto> \<tau>, a \<mapsto> T, b \<mapsto> S)) A of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using * by metis
        moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S, x \<mapsto> \<tau>)) A of None \<Rightarrow> None | Some \<sigma> \<Rightarrow> Some (TArr \<tau> \<sigma>))"
          using \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> fun_upd_twist by metis
        moreover have "... = ptrm_infer_type (\<Gamma>(a \<mapsto> T, b \<mapsto> S)) (PFn x \<tau> A)" by simp
        ultimately show ?thesis by metis
      next
    qed
  next
  case (PPair A B)
    thus ?case by simp
  next
  case (PFst P)
    thus ?case by simp
  next
  case (PSnd P)
    thus ?case by simp
  next
qed

lemma ptrm_infer_type_swp:
  assumes "a \<noteq> b" "b \<notin> ptrm_fvs X"
  shows "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) X = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> X)"
using assms proof(induction X arbitrary: \<tau> \<Gamma>)
  case (PUnit)
    thus ?case by simp
  next
  case (PVar x)
    hence "x \<noteq> b" by simp
    consider "x = a" | "x \<noteq> a" by auto
    thus ?case proof(cases)
      case 1
        hence "[a \<leftrightarrow> b] \<bullet> (PVar x) = PVar b"
        and   "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PVar x) = Some \<tau>" using prm_unit_action by auto
        thus ?thesis by auto
      next

      case 2
        hence *: "[a \<leftrightarrow> b] \<bullet> PVar x = PVar x" using \<open>x \<noteq> b\<close> prm_unit_inaction by simp
        consider "\<exists>\<sigma>. \<Gamma> x = Some \<sigma>" | "\<Gamma> x = None" by auto
        thus ?thesis proof(cases)
          assume "\<exists>\<sigma>. \<Gamma> x = Some \<sigma>"
          from this obtain \<sigma> where "\<Gamma> x = Some \<sigma>" by auto
          thus ?thesis using * \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> by auto
          next
  
          assume "\<Gamma> x = None"
          thus ?thesis using * \<open>x \<noteq> a\<close> \<open>x \<noteq> b\<close> by auto
        qed
      next
    qed
  next
  case (PApp A B)
    have "b \<notin> ptrm_fvs A" and "b \<notin> ptrm_fvs B" using PApp.prems by auto
    hence "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) A = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A)"
    and   "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) B = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> B)"
      using PApp.IH assms by metis+
    
    thus ?case by (metis ptrm_apply_prm.simps(3) ptrm_infer_type.simps(3))
  next
  case (PFn x \<sigma> A)
    consider "b \<noteq> x \<and> b \<notin> ptrm_fvs A" | "b = x" using PFn.prems by auto
    thus ?case proof(cases)
      case 1
        hence "b \<noteq> x" "b \<notin> ptrm_fvs A" by auto
        hence *: "\<And>\<tau> \<Gamma>. ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) A = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A)"
          using PFn.IH assms by metis
        consider "a = x" | "a \<noteq> x" by auto
        thus ?thesis proof(cases)
          case 1
            hence "ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PFn x \<sigma> A) = ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PFn a \<sigma> A)"
            and "
              ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> PFn x \<sigma> A) =
              ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) (PFn b \<sigma> ([a \<leftrightarrow> b] \<bullet> A))"
            by (auto simp add: prm_unit_action)
            thus ?thesis using * ptrm_infer_type.simps(4) fun_upd_upd by metis
          next
  
          case 2
            hence
              "ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> PFn x \<sigma> A)
             = ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)) (PFn x \<sigma> ([a \<leftrightarrow> b] \<bullet> A))"
              using \<open>b \<noteq> x\<close> by (simp add: prm_unit_inaction)
            moreover have "... = (case ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>, x \<mapsto> \<sigma>)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma>' \<Rightarrow> Some (TArr \<sigma> \<sigma>'))"
              by simp
            moreover have "... = (case ptrm_infer_type (\<Gamma>(x \<mapsto> \<sigma>, b \<mapsto> \<tau>)) ([a \<leftrightarrow> b] \<bullet> A) of None \<Rightarrow> None | Some \<sigma>' \<Rightarrow> Some (TArr \<sigma> \<sigma>'))"
              using \<open>b \<noteq> x\<close> fun_upd_twist by metis
            moreover have "... = (case ptrm_infer_type (\<Gamma>(x \<mapsto> \<sigma>, a \<mapsto> \<tau>)) A of None \<Rightarrow> None | Some \<sigma>' \<Rightarrow> Some (TArr \<sigma> \<sigma>'))"
              using * by metis
            moreover have "... = (case ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>, x \<mapsto> \<sigma>)) A of None \<Rightarrow> None | Some \<sigma>' \<Rightarrow> Some (TArr \<sigma> \<sigma>'))"
              using \<open>a \<noteq> x\<close> fun_upd_twist by metis
            moreover have "... = ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)) (PFn x \<sigma> A)"
              by simp
            ultimately show ?thesis by metis
          next
        qed
      next

      case 2
        hence "a \<noteq> x" using assms by auto
        have "
          ptrm_infer_type (\<Gamma>(a \<mapsto> \<tau>)(b \<mapsto> \<sigma>)) A =
          ptrm_infer_type (\<Gamma>(b \<mapsto> \<tau>)(a \<mapsto> \<sigma>)) ([a \<leftrightarrow> b] \<bullet> A)
        " using ptrm_infer_type_swp_types using \<open>a \<noteq> b\<close> fun_upd_twist by metis
        thus ?thesis
          using \<open>b = x\<close> prm_unit_action prm_unit_commutes
          using ptrm_infer_type.simps(4) ptrm_apply_prm.simps(4) by metis
      next
    qed
  next
  case (PPair A B)
    thus ?case by simp
  next
  case (PFst P)
    thus ?case by simp
  next
  case (PSnd P)
    thus ?case by simp
  next
qed

lemma ptrm_infer_type_alpha_equiv:
  assumes "X \<approx> Y"
  shows "ptrm_infer_type \<Gamma> X = ptrm_infer_type \<Gamma> Y"
using assms proof(induction arbitrary: \<Gamma>)
  case (fn2 a b A B T \<Gamma>)
    hence "ptrm_infer_type (\<Gamma>(a \<mapsto> T)) A = ptrm_infer_type (\<Gamma>(b \<mapsto> T)) B"
      using ptrm_infer_type_swp prm_unit_commutes by metis
    thus ?case by simp
  next
qed auto

end
