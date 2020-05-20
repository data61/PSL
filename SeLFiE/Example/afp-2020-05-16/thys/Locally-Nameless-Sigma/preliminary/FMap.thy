(*  Title:      FMap.thy
    Author:     Ludovic Henrio and Florian Kammuller, 2006

Finite maps for Sigma-calculus
Idea use axiomatic type classes to preserve
usability of datatype afterwards, i.e. definition
of an object as a finite map of labels to fields in
a datatype.
*)

section \<open>Finite maps with axclasses\<close>

theory FMap imports ListPre begin

type_synonym ('a, 'b) fmap = "('a :: finite) \<rightharpoonup> 'b" (infixl "-~>" 50)

class inftype =
assumes infinite: "\<not>finite UNIV"

theorem fset_induct:
  "P {} \<Longrightarrow> (\<And>x (F::('a::finite)set). x \<notin> F \<Longrightarrow> P F \<Longrightarrow> P (insert x F)) \<Longrightarrow> P F"
proof (rule_tac P=P and F=F in finite_induct)
  from finite_subset[OF subset_UNIV] show "finite F" by auto
next
  assume "P {}" thus "P {}" by simp
next
  fix x F 
  assume "\<And>x F. \<lbrakk> x \<notin> F; P F \<rbrakk> \<Longrightarrow> P (insert x F)" and "x \<notin> F" and "P F"
  thus "P (insert x F)" by simp
qed

theorem fmap_unique: "x = y \<Longrightarrow> (f::('a,'b)fmap) x = f y"
  by (erule ssubst, rule refl)

theorem fmap_case:
  "(F::('a -~> 'b)) = Map.empty \<or> (\<exists>x y (F'::('a -~> 'b)). F = F'(x \<mapsto> y))"
proof (cases "F = Map.empty")
  case True thus ?thesis by (rule disjI1)
next
  case False thus ?thesis
  proof (simp)
    from \<open>F \<noteq> Map.empty\<close> have "\<exists>x. F x \<noteq> None"
    proof (rule contrapos_np)
      assume "\<not> (\<exists>x. F x \<noteq> None)"
      hence "\<forall>x. F x = None" by simp
      hence "\<And>x. F x = None" by simp
      thus "F = Map.empty" by (rule ext)
    qed
    thus "\<exists>x y F'. F = F'(x \<mapsto> y)"
    proof
      fix x assume "F x \<noteq> None"
      hence "\<And>y. F y = (F(x \<mapsto> the (F x))) y" by auto
      hence "F = F(x \<mapsto> the (F x))" by (rule ext)
      thus ?thesis by auto
    qed
  qed
qed

(* define the witness as a constant function so it may be used in the proof of
the induction scheme below *)
definition  
  set_fmap :: "'a -~> 'b \<Rightarrow> ('a * 'b)set" where
  "set_fmap F = {(x, y). x \<in> dom F \<and> F x = Some y}"

definition
  pred_set_fmap :: "(('a -~> 'b) \<Rightarrow> bool) \<Rightarrow> (('a * 'b)set) \<Rightarrow> bool" where
  "pred_set_fmap P = (\<lambda>S. P (\<lambda>x. if x \<in> fst ` S 
                                  then (THE y. (\<exists>z. y = Some z \<and> (x, z) \<in> S)) 
                                  else None))" 

definition
  fmap_minus_direct :: "[('a -~> 'b), ('a * 'b)] \<Rightarrow> ('a -~> 'b)" (infixl "--" 50) where
  "F -- x = (\<lambda>z. if (fst x = z \<and> ((F (fst x)) = Some (snd x))) 
                   then None 
                   else (F z))"

lemma insert_lem : "insert x A = B \<Longrightarrow> x \<in> B"
  by auto

lemma fmap_minus_fmap: 
  fixes F x a b
  assumes "(F -- x) a = Some b"
  shows "F a = Some b"
proof (rule ccontr, cases "F a")
  case None hence "a \<notin> dom F" by auto
  hence "(F -- x) a = None" 
    unfolding fmap_minus_direct_def by auto
  with \<open>(F -- x) a = Some b\<close> show False by simp
next
  assume "F a \<noteq> Some b"
  case (Some y) thus False
  proof (cases "fst x = a")
    case True thus False
    proof (cases "snd x = y")
      case True with \<open>F a = Some y\<close> \<open>fst x = a\<close> 
      have "(F -- x) a = None" unfolding fmap_minus_direct_def by auto
      with \<open>(F -- x) a = Some b\<close> show False by simp
    next
      case False with \<open>F a = Some y\<close> \<open>fst x = a\<close> 
      have "F (fst x) \<noteq> Some (snd x)" by auto
      with \<open>(F -- x) a = Some b\<close> have "F a = Some b" 
        unfolding fmap_minus_direct_def by auto
      with \<open>F a \<noteq> Some b\<close> show False by simp
    qed
  next
    case False with \<open>(F -- x) a = Some b\<close> 
    have "F a = Some b" unfolding fmap_minus_direct_def by auto
    with \<open>F a \<noteq> Some b\<close> show False by simp
  qed
qed

lemma set_fmap_minus_iff: 
  "set_fmap ((F::(('a::finite) -~> 'b)) -- x) = set_fmap F - {x}"
  unfolding set_fmap_def 
proof (auto)
  fix a b assume "(F -- x) a = Some b" from fmap_minus_fmap[OF this]
  show "\<exists>y. F a = Some y" by blast
next
  fix a b assume "(F -- x) a = Some b" from fmap_minus_fmap[OF this]
  show "F a = Some b" by assumption
next
  fix a b assume "(F -- (a, b)) a = Some b" 
  with fmap_minus_fmap[OF this] show False 
    unfolding fmap_minus_direct_def by auto
next
  fix a b assume "(a,b) \<noteq> x" and "F a = Some b"
  hence "fst x \<noteq> a \<or> F (fst x) \<noteq> Some (snd x)" by auto
  with \<open>F a = Some b\<close> show "\<exists>y. (F -- x) a = Some y" 
    unfolding fmap_minus_direct_def by (rule_tac x = b in exI, simp)
next
  fix a b assume "(a,b) \<noteq> x" and "F a = Some b"
  hence "fst x \<noteq> a \<or> F (fst x) \<noteq> Some (snd x)" by auto
  with \<open>F a = Some b\<close> show "(F -- x) a = Some b" 
    unfolding fmap_minus_direct_def by simp  
qed

lemma set_fmap_minus_insert:
  fixes F :: "('a::finite * 'b)set" and  F':: "('a::finite) -~> 'b" and x
  assumes "x \<notin> F" and "insert x F = set_fmap F'"
  shows "F = set_fmap (F' -- x)"
proof -
  from \<open>x \<notin> F\<close> sym[OF \<open>insert x F = set_fmap F'\<close>] set_fmap_minus_iff[of F' x] 
  show ?thesis by simp
qed

lemma notin_fmap_minus: "x \<notin> set_fmap ((F::(('a::finite) -~> 'b)) -- x)"
  by (auto simp: set_fmap_minus_iff)

lemma fst_notin_fmap_minus_dom:
  fixes F x and F' :: "('a::finite) -~> 'b"
  assumes "insert x F = set_fmap F'"
  shows "fst x \<notin> dom (F' -- x)"
proof (rule ccontr, auto)
  fix y assume "(F' -- x) (fst x) = Some y"
  with notin_fmap_minus[of x F'] 
  have "y \<noteq> snd x"
    unfolding set_fmap_def by auto
  moreover
  from insert_lem[OF \<open>insert x F = set_fmap F'\<close>] 
  have "F' (fst x) = Some (snd x)"
    unfolding set_fmap_def by auto
  ultimately show False 
    using fmap_minus_fmap[OF \<open>(F' -- x) (fst x) = Some y\<close>]
    by simp
qed

lemma  set_fmap_pair: 
  "x \<in> set_fmap F \<Longrightarrow> (fst x \<in> dom F \<and> snd x = the (F (fst x)))"
  by (simp add: set_fmap_def, auto)

lemma  set_fmap_inv1: 
  "\<lbrakk> fst x \<in> dom F; snd x = the (F (fst x)) \<rbrakk> \<Longrightarrow> (F -- x)(fst x \<mapsto> snd x) = F"
proof (rule ext)
  fix xa assume "fst x \<in> dom F" and "snd x = the (F (fst x))"
  thus "((F -- x)(fst x \<mapsto> snd x)) xa = F xa"
    unfolding fmap_minus_direct_def
    by (case_tac "xa = fst x", auto)
qed

lemma set_fmap_inv2: 
  "fst x \<notin> dom F \<Longrightarrow> insert x (set_fmap F) = set_fmap (F(fst x \<mapsto> snd x))"
  unfolding set_fmap_def
proof
  assume "fst x \<notin> dom F"
  thus
    "insert x {(x, y). x \<in> dom F \<and> F x = Some y} \<subseteq> 
    {(xa, y). xa \<in> dom (F(fst x \<mapsto> snd x)) \<and> (F(fst x \<mapsto> snd x)) xa = Some y}"
    by force
next
  have
    "\<And>z. z \<in> {(xa, y). xa \<in> dom (F(fst x \<mapsto> snd x)) 
                     \<and> (F(fst x \<mapsto> snd x)) xa = Some y}
    \<Longrightarrow> z \<in> insert x {(x, y). x \<in> dom F \<and> F x = Some y}"
    proof -
      fix z
      assume 
        z: "z \<in> {(xa, y). xa \<in> dom (F(fst x \<mapsto> snd x)) 
                     \<and> (F(fst x \<mapsto> snd x)) xa = Some y}"
      hence "z = x \<or> ((fst z) \<in> dom F \<and> F (fst z) = Some (snd z))"
      proof (cases "fst x = fst z")
        case True thus ?thesis using z by auto
      next
        case False thus ?thesis using z by auto
      qed
      thus "z \<in> insert x {(x, y). x \<in> dom F \<and> F x = Some y}" by fastforce
    qed
  thus 
    "{(xa, y). xa \<in> dom (F(fst x \<mapsto> snd x)) \<and> (F(fst x \<mapsto> snd x)) xa = Some y} \<subseteq> 
    insert x {(x, y). x \<in> dom F \<and> F x = Some y}" by auto
qed

lemma rep_fmap_base: "P (F::('a  -~> 'b)) = (pred_set_fmap P)(set_fmap F)"
  unfolding pred_set_fmap_def set_fmap_def
proof (rule_tac f = P in arg_cong)
  have 
    "\<And>x. F x = 
         (\<lambda>x. if x \<in> fst ` {(x, y). x \<in> dom F \<and> F x = Some y}
               then THE y. \<exists>z. y = Some z 
                             \<and> (x, z) \<in> {(x, y). x \<in> dom F \<and> F x = Some y}
               else None) x"
  proof auto
    fix a b
    assume "F a = Some b"
    hence "\<exists>!x. x = Some b \<and> a \<in> dom F"
    proof (rule_tac a = "F a" in ex1I)
      assume "F a = Some b"
      thus "F a = Some b \<and> a \<in> dom F" 
        by (simp add: dom_def)
    next
      fix x assume "F a = Some b" and "x = Some b \<and> a \<in> dom F"
      thus "x = F a" by simp
    qed
    hence "(THE y. y = Some b \<and> a \<in> dom F) = Some b \<and> a \<in> dom F" 
      by (rule theI')
    thus "Some b = (THE y. y = Some b \<and> a \<in> dom F)" 
      by simp
  next
    fix x assume nin_x: "x \<notin> fst ` {(x, y). x \<in> dom F \<and> F x = Some y}"
    thus "F x = None"
    proof (cases "F x")
      case None thus ?thesis by assumption
    next
      case (Some a)
      hence "x \<in> fst ` {(x, y). x \<in> dom F \<and> F x = Some y}"
        by (simp add: image_def dom_def)
      with nin_x show ?thesis by simp
    qed
  qed
  thus 
    "F = (\<lambda>x. if x \<in> fst ` {(x, y). x \<in> dom F \<and> F x = Some y}
               then THE y. \<exists>z. y = Some z 
                             \<and> (x, z) \<in> {(x, y). x \<in> dom F \<and> F x = Some y}
               else None)"
    by (rule ext)
qed

lemma rep_fmap: 
  "\<exists>(Fp ::('a * 'b)set) (P'::('a * 'b)set \<Rightarrow> bool). P (F::('a -~> 'b)) = P' Fp"
proof -
  from rep_fmap_base show ?thesis by blast
qed

theorem finite_fsets: "finite (F::('a::finite)set)"
proof -
  from finite_subset[OF subset_UNIV] show "finite F" by auto
qed

lemma finite_dom_fmap: "finite (dom (F::('a -~> 'b))::('a::finite)set)"
  by (rule finite_fsets)

lemma finite_fmap_ran: "finite (ran (F::(('a::finite) -~> 'b)))"
  unfolding ran_def
proof -
  from finite_dom_fmap finite_imageI 
  have "finite ((\<lambda>x. the (F x)) ` (dom F))" 
    by blast
  moreover
  have "{b. \<exists>a. F a = Some b} = (\<lambda>x. the (F x)) ` (dom F)"
    unfolding image_def dom_def by force
  ultimately
  show "finite {b. \<exists>a. F a = Some b}"  by simp
qed

lemma finite_fset_map: "finite (set_fmap (F::(('a::finite) -~> 'b)))"
proof -
  from finite_cartesian_product[OF finite_dom_fmap finite_fmap_ran]
  have "finite (dom F \<times> ran F)" .
  moreover
  have "set_fmap F \<subseteq> dom F \<times> ran F"
    unfolding set_fmap_def dom_def ran_def by fastforce
  ultimately
  show ?thesis using finite_subset by auto
qed

lemma rep_fmap_imp: 
  "\<forall>F x z. x \<notin> dom (F::('a -~> 'b)) \<longrightarrow> P F \<longrightarrow> P (F(x \<mapsto> z))
  \<Longrightarrow> (\<forall>F x z. x \<notin> fst ` (set_fmap F) \<longrightarrow> (pred_set_fmap P)(set_fmap F) 
        \<longrightarrow> (pred_set_fmap P) (insert (x,z) (set_fmap F)))"
proof (clarify)
  fix P F x z
  assume 
    "\<forall>F x z. x \<notin> dom (F::('a -~> 'b)) \<longrightarrow> P F \<longrightarrow> P (F(x \<mapsto> z))" and
    "x \<notin> fst ` set_fmap F" and "(pred_set_fmap P)(set_fmap F)"
  hence notin: "x \<notin> dom F"
    unfolding set_fmap_def image_def dom_def by simp
  moreover
  from \<open>pred_set_fmap P (set_fmap F)\<close> have "P F" by (simp add: rep_fmap_base)
  ultimately
  have "P (F(x \<mapsto> z))" using \<open>\<forall>F x z. x \<notin> dom F \<longrightarrow> P F \<longrightarrow> P (F(x \<mapsto> z))\<close> 
    by blast
  hence "(pred_set_fmap P) (set_fmap (F(x \<mapsto> z)))"
    by (simp add: rep_fmap_base)
  moreover
  from notin 
  have "(insert (x,z) (set_fmap F)) = (set_fmap (F(fst (x,z) \<mapsto> snd (x,z))))"
    by (simp add: set_fmap_inv2)
  ultimately
  show "(pred_set_fmap P) (insert (x,z) (set_fmap F))" by simp
qed

lemma empty_dom: 
  fixes g
  assumes "{} = dom g"
  shows "g = Map.empty"
proof 
  fix x from assms show "g x = None" by auto
qed

theorem fmap_induct[rule_format, case_names empty insert]:
  fixes  P  :: "(('a :: finite) -~> 'b) \<Rightarrow> bool" and  F' :: "('a  -~> 'b)"
  assumes 
  "P Map.empty" and
  "\<forall>(F::('a -~> 'b)) x z. x \<notin> dom F \<longrightarrow> P F \<longrightarrow> P (F(x \<mapsto> z))"
  shows "P F'"
proof -
  {
    fix F :: "('a \<times> 'b) set" assume "finite F"
    hence "\<forall>F'. F = set_fmap F' \<longrightarrow> pred_set_fmap P (set_fmap F')"
    proof (induct F)
      case empty thus ?case
      proof (intro strip)
        fix F' :: "'a -~> 'b" assume "{} = set_fmap F'"
        hence "\<And>a. F' a = None" unfolding set_fmap_def by auto
        hence "F' = Map.empty" by (rule ext)
        with \<open>P Map.empty\<close> rep_fmap_base[of P Map.empty] 
        show "pred_set_fmap P (set_fmap F')" by simp
      qed
    next
      case (insert x Fa) thus ?case
      proof (intro strip)
        fix Fb :: "'a -~> 'b"
        assume "insert x Fa = set_fmap Fb"
        from 
          set_fmap_minus_insert[OF \<open>x \<notin> Fa\<close> this]
          \<open>\<forall>F'. Fa = set_fmap F' \<longrightarrow> pred_set_fmap P (set_fmap F')\<close> 
          rep_fmap_base[of P "Fb -- x"]
        have "P (Fb -- x)" by blast
        with 
          \<open>\<forall>F x z. x \<notin> dom F \<longrightarrow> P F \<longrightarrow> P (F(x \<mapsto> z))\<close> 
          fst_notin_fmap_minus_dom[OF \<open>insert x Fa = set_fmap Fb\<close>]
        have "P ((Fb -- x)(fst x \<mapsto> snd x))" by blast
        moreover
        from 
          insert_absorb[OF insert_lem[OF \<open>insert x Fa = set_fmap Fb\<close>]]
          set_fmap_minus_iff[of Fb x]
          set_fmap_inv2[OF 
           fst_notin_fmap_minus_dom[OF \<open>insert x Fa = set_fmap Fb\<close>]] 
        have "set_fmap Fb = set_fmap ((Fb -- x)(fst x \<mapsto> snd x))"
          by simp
        ultimately
        show "pred_set_fmap P (set_fmap Fb)" 
          using rep_fmap_base[of P "(Fb -- x)(fst x \<mapsto> snd x)"]
          by simp
      qed
    qed
  } 
  from this[OF finite_fset_map[of F']]
       rep_fmap_base[of P F']
  show "P F'" by blast
qed

lemma fmap_induct3[consumes 2, case_names empty insert]:
  "\<And>(F2::('a::finite) -~> 'b) (F3::('a -~> 'b)).
   \<lbrakk> dom (F1::('a -~> 'b)) = dom F2; dom F3 = dom F1; 
     P Map.empty Map.empty Map.empty;
     \<And>x a b c (F1::('a -~> 'b)) (F2::('a -~> 'b)) (F3::('a -~> 'b)).
     \<lbrakk> P F1 F2 F3; dom F1 = dom F2; dom F3 = dom F1; x \<notin> dom F1 \<rbrakk>
     \<Longrightarrow> P (F1(x \<mapsto> a)) (F2(x \<mapsto> b)) (F3(x \<mapsto> c)) \<rbrakk>
  \<Longrightarrow> P F1 F2 F3"
proof (induct F1 rule: fmap_induct)
  case empty
  from \<open>dom Map.empty = dom F2\<close> have "F2 = Map.empty" by (simp add: empty_dom)
  moreover
  from \<open>dom F3 = dom Map.empty\<close> have "F3 = Map.empty" by (simp add: empty_dom)
  ultimately
  show ?case using \<open>P Map.empty Map.empty Map.empty\<close> by simp
next
  case (insert F x y) thus ?case
  proof (cases "F2 = Map.empty")
    case True with \<open>dom (F(x \<mapsto> y)) = dom F2\<close> 
    have "dom (F(x \<mapsto> y)) = {}" by auto
    thus ?thesis by auto
  next
    case False thus ?thesis
    proof (cases "F3 = Map.empty")
      case True with \<open>dom F3 = dom (F(x \<mapsto> y))\<close> 
      have "dom (F(x \<mapsto> y)) = {}" by simp
      thus ?thesis by simp
    next
      case False thus ?thesis
      proof -
        from \<open>F2 \<noteq> Map.empty\<close> 
        have "\<forall>l\<in>dom F2. \<exists>f'. F2 = f'(l \<mapsto> the (F2 l)) \<and> l \<notin> dom f'"
          by (simp add: one_more_dom)
        moreover
        from \<open>dom (F(x \<mapsto> y)) = dom F2\<close> have "x \<in> dom F2" by force
        ultimately have "\<exists>f'. F2 = f'(x \<mapsto> the (F2 x)) \<and> x \<notin> dom f'" by blast
        then obtain F2' where "F2 = F2'(x \<mapsto> the (F2 x))" and "x \<notin> dom F2'" 
          by auto

        from \<open>F3 \<noteq> Map.empty\<close> 
        have "\<forall>l\<in>dom F3. \<exists>f'. F3 = f'(l \<mapsto> the (F3 l)) \<and> l \<notin> dom f'"
          by (simp add: one_more_dom)
        moreover from \<open>dom F3 = dom (F(x \<mapsto> y))\<close> have "x \<in> dom F3" by force
        ultimately have "\<exists>f'. F3 = f'(x \<mapsto> the (F3 x)) \<and> x \<notin> dom f'" by blast
        then obtain F3' where "F3 = F3'(x \<mapsto> the (F3 x))" and "x \<notin> dom F3'" 
          by auto

        show ?thesis
        proof -
          from \<open>dom (F(x \<mapsto> y)) = dom F2\<close> \<open>F2 = F2'(x \<mapsto> the (F2 x))\<close>
          have "dom (F(x \<mapsto> y)) = dom (F2'(x \<mapsto> the (F2 x)))" by simp
          with \<open>x \<notin> dom F\<close> \<open>x \<notin> dom F2'\<close> have "dom F = dom F2'" by auto
          
          moreover
          from \<open>dom F3 = dom (F(x \<mapsto> y))\<close> \<open>F3 = F3'(x \<mapsto> the (F3 x))\<close>
          have "dom (F(x \<mapsto> y)) = dom (F3'(x \<mapsto> the (F3 x)))" by simp
          with \<open>x \<notin> dom F\<close> \<open>x \<notin> dom F3'\<close> have "dom F3' = dom F" by auto

          ultimately have "P F F2' F3'" using insert by simp

          with 
            \<open>\<And>F1 F2 F3 x a b c.
              \<lbrakk> P F1 F2 F3; dom F1 = dom F2; dom F3 = dom F1; x \<notin> dom F1 \<rbrakk>
              \<Longrightarrow> P (F1(x \<mapsto> a)) (F2(x \<mapsto> b)) (F3(x \<mapsto> c))\<close>
            \<open>dom F = dom F2'\<close>
            \<open>dom F3' = dom F\<close>
            \<open>x \<notin> dom F\<close>
          have "P (F(x \<mapsto> y)) (F2'(x \<mapsto> the (F2 x))) (F3'(x \<mapsto> the (F3 x)))" 
            by simp
          with \<open>F2 = F2'(x \<mapsto> the (F2 x))\<close> \<open>F3 = F3'(x \<mapsto> the (F3 x))\<close>
          show "P (F(x \<mapsto> y)) F2 F3" by simp
        qed
      qed
    qed
  qed
qed

lemma fmap_ex_cof2:
  "\<And>(P::'c \<Rightarrow> 'c \<Rightarrow> 'b option \<Rightarrow> 'b option \<Rightarrow> 'a \<Rightarrow> bool)
     (f'::('a::finite) -~> 'b).
  \<lbrakk> dom f' = dom (f::('a -~> 'b)); 
    \<forall>l\<in>dom f. (\<exists>L. finite L 
                  \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p
                      \<longrightarrow> P s p (f l) (f' l) l)) \<rbrakk>
  \<Longrightarrow> \<exists>L. finite L \<and> (\<forall>l\<in>dom f. (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p 
                                   \<longrightarrow> P s p (f l) (f' l) l))"
proof (induct f rule: fmap_induct)
  case empty thus ?case by blast
next
  case (insert f l t P f') note imp = this(2) and pred = this(4)
  define pred_cof where "pred_cof L b b' l \<longleftrightarrow> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P s p b b' l)"
    for L b b' l
  from 
    map_upd_nonempty[of f l t] \<open>dom f' = dom (f(l \<mapsto> t))\<close>
    one_more_dom[of l f']
  obtain f'a where 
    "f' = f'a(l \<mapsto> the(f' l))" and "l \<notin> dom f'a" and
    "dom (f'a(l \<mapsto> the(f' l))) = dom (f(l \<mapsto> t))"
    by auto
  from \<open>l \<notin> dom f\<close>
  have
    fla: "\<forall>la\<in>dom f. f la = (f(l \<mapsto> t)) la" and
    "\<forall>la\<in>dom f. f'a la = (f'a(l \<mapsto> the(f' l))) la"
    by auto
  with \<open>f' = f'a(l \<mapsto> the(f' l))\<close> 
  have f'ala: "\<forall>la\<in>dom f. f'a la = f' la" by simp
  have "\<exists>L. finite L \<and> (\<forall>la\<in>dom f. pred_cof L (f la) (f'a la) la)"
    unfolding pred_cof_def
  proof 
    (intro imp[OF insert_dom_less_eq[OF \<open>l \<notin> dom f'a\<close> \<open>l \<notin> dom f\<close> 
                                        \<open>dom (f'a(l \<mapsto> the(f' l))) = dom (f(l \<mapsto> t))\<close>]],
      intro strip)
    fix la assume "la \<in> dom f"
    with fla f'ala 
    have 
      "la \<in> dom (f(l \<mapsto> t))" and 
      "f la = (f(l \<mapsto> t)) la" and "f'a la = f' la"
      by auto
    with pred
    show "\<exists>L. finite L \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P s p (f la) (f'a la) la)"
      by (elim ssubst, blast)
  qed
  with fla f'ala obtain L where 
    "finite L" and predf: "\<forall>la\<in>dom f. pred_cof L ((f(l \<mapsto> t)) la) (f' la) la"
    by auto
  moreover
  have "l \<in> dom (f(l \<mapsto> t))" by simp
  with pred obtain L' where
    "finite L'" and predfl: "pred_cof L' ((f(l \<mapsto> t)) l) (f' l) l"
    unfolding pred_cof_def
    by blast
  ultimately show ?case
  proof (rule_tac x = "L \<union> L'" in exI, 
      intro conjI, simp, intro strip)
    fix s p la assume 
      sp: "s \<notin> L \<union> L' \<and> p \<notin> L \<union> L' \<and> s \<noteq> p" and indom: "la \<in> dom (f(l \<mapsto> t))"
    show "P s p ((f(l \<mapsto> t)) la) (f' la) la"
    proof (cases "la = l")
      case True with sp predfl show ?thesis 
        unfolding pred_cof_def
        by simp
    next
      case False with indom sp predf show ?thesis 
        unfolding pred_cof_def
        by force
    qed
  qed
qed

lemma fmap_ex_cof:
  fixes
  P :: "'c \<Rightarrow> 'c \<Rightarrow> 'b option \<Rightarrow> ('a::finite) \<Rightarrow> bool"
  assumes
  "\<forall>l\<in>dom (f::('a -~> 'b)).
  (\<exists>L. finite L \<and> (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P s p (f l) l))"
  shows
  "\<exists>L. finite L \<and> (\<forall>l\<in>dom f. (\<forall>s p. s \<notin> L \<and> p \<notin> L \<and> s \<noteq> p \<longrightarrow> P s p (f l) l))"
  using assms fmap_ex_cof2[of f f  "\<lambda>s p b b' l. P s p b l"] by auto

lemma fmap_ball_all2:
  fixes 
  Px :: "'c \<Rightarrow> 'd \<Rightarrow> bool" and 
  P :: "'c \<Rightarrow> 'd \<Rightarrow> 'b option \<Rightarrow> bool"
  assumes
  "\<forall>l\<in>dom (f::('a::finite) -~> 'b). \<forall>(x::'c) (y::'d). Px x y \<longrightarrow> P x y (f l)"
  shows
  "\<forall>x y. Px x y \<longrightarrow> (\<forall>l\<in>dom f. P x y (f l))"
proof (intro strip)
  fix x y l assume "Px x y" and "l \<in> dom f"
  with assms show "P x y (f l)" by blast
qed

lemma fmap_ball_all2':
  fixes 
  Px :: "'c \<Rightarrow> 'd \<Rightarrow> bool" and 
  P :: "'c \<Rightarrow> 'd \<Rightarrow> 'b option \<Rightarrow> ('a::finite) \<Rightarrow> bool"
  assumes
  "\<forall>l\<in>dom (f::('a -~> 'b)). \<forall>(x::'c) (y::'d). Px x y \<longrightarrow> P x y (f l) l"
  shows
  "\<forall>x y. Px x y \<longrightarrow> (\<forall>l\<in>dom f. P x y (f l) l)"
proof (intro strip)
  fix x y l assume "Px x y" and "l \<in> dom f"
  with assms show "P x y (f l) l" by blast
qed

lemma fmap_ball_all3:
  fixes 
  Px :: "'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> bool" and 
  P :: "'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'b option \<Rightarrow> 'b option \<Rightarrow> bool" and
  f :: "('a::finite) -~> 'b" and f' :: "'a -~> 'b"
  assumes
  "dom f' = dom f" and
  "\<forall>l\<in>dom f.
     \<forall>(x::'c) (y::'d) (z::'e). Px x y z \<longrightarrow> P x y z (f l) (f' l)"
  shows
  "\<forall>x y z. Px x y z \<longrightarrow> (\<forall>l\<in>dom f. P x y z (f l) (f' l))"
proof (intro strip)
  fix x y z l assume "Px x y z" and "l \<in> dom f"
  with assms show "P x y z (f l) (f' l)" by blast
qed

lemma fmap_ball_all4':
  fixes 
  Px :: "'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> bool" and 
  P :: "'c \<Rightarrow> 'd \<Rightarrow> 'e \<Rightarrow> 'f \<Rightarrow> 'b option \<Rightarrow> ('a::finite) \<Rightarrow> bool"
  assumes
  "\<forall>l\<in>dom (f::('a -~> 'b)). 
    \<forall>(x::'c) (y::'d) (z::'e) (a::'f). Px x y z a \<longrightarrow> P x y z a (f l) l"
  shows
  "\<forall>x y z a. Px x y z a \<longrightarrow> (\<forall>l\<in>dom f. P x y z a (f l) l)"
proof (intro strip)
  fix x y z a l assume "Px x y z a" and "l \<in> dom f"
  with assms show "P x y z a (f l) l" by blast
qed

end
