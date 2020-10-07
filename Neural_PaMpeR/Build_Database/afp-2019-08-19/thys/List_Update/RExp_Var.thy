(*  Title:       Enable Checking of Equivalence of Regular Expressions with Variables
    Author:      Max Haslbeck
    Reference:   http://www4.in.tum.de/lehre/vorlesungen/theo/SS10/vorlesung.shtml p.96ff
*)
section \<open>Equivalence of Regular Expression with Variables\<close>

theory RExp_Var
imports "Regular-Sets.Equivalence_Checking"
begin

(* even Atoms \<rightarrow> normal Atoms
    odd Atoms \<rightarrow> Variables *)
fun castdown :: "nat rexp \<Rightarrow> nat rexp" where
  "castdown Zero = Zero"
| "castdown One = One"
| "castdown (Plus a b) = Plus (castdown a) (castdown b)"
| "castdown (Times a b) = Times (castdown a) (castdown b)"
| "castdown (Star a) = Star (castdown a)"
| "castdown (Atom x) = (Atom (x div 2))"

fun castup :: "nat rexp \<Rightarrow> nat rexp" where
  "castup Zero = Zero"
| "castup One = One"
| "castup (Plus a b) = Plus (castup a) (castup b)"
| "castup (Times a b) = Times (castup a) (castup b)"
| "castup (Star a) = Star (castup a)"
| "castup (Atom x) = Atom (2*x)"

lemma "castdown (castup r) = r"
apply(induct r) by(auto)


fun substvar :: "nat \<Rightarrow> (nat \<Rightarrow> ((nat rexp) option)) \<Rightarrow> nat rexp" where
  "substvar i \<sigma> = (case \<sigma> i of Some x \<Rightarrow> x
                              | None \<Rightarrow> Atom (2*i+1))"

fun w2rexp :: "nat list \<Rightarrow> nat rexp" where
  "w2rexp [] = One"
| "w2rexp (a#as) = Times (Atom a) (w2rexp as)"

lemma "lang (w2rexp as) = { as }"
apply(induct as)
  apply(simp)
  by(simp add: conc_def)



fun subst :: "nat rexp \<Rightarrow> (nat \<Rightarrow> nat rexp option) \<Rightarrow> nat rexp" where
  "subst Zero _ = Zero"
| "subst One _ = One"
| "subst (Atom i) \<sigma> = (if i mod 2 = 0 then Atom i else substvar (i div 2) \<sigma>)"
| "subst (Plus a b) \<sigma> = Plus (subst a \<sigma>) (subst b \<sigma>)"
| "subst (Times a b) \<sigma> = Times (subst a \<sigma>) (subst b \<sigma>)"
| "subst (Star a) \<sigma> = Star (subst a \<sigma>)"


lemma subst_w2rexp: "lang (subst (w2rexp (xs @ ys)) \<sigma>) = lang (subst (w2rexp xs) \<sigma>) @@ lang (subst (w2rexp ys) \<sigma>)"
proof(induct xs)
  case (Cons x xs)
  have "lang (subst (w2rexp ((x # xs) @ ys)) \<sigma>)
        = lang (subst (Times (Atom x) (w2rexp (xs @ ys))) \<sigma>)" by simp
  also have "\<dots> = lang (Times (subst (Atom x) \<sigma>) (subst (w2rexp (xs @ ys)) \<sigma>))" by simp
  also have "\<dots> = lang (subst (Atom x) \<sigma>) @@ (lang (subst (w2rexp (xs @ ys)) \<sigma>))" by simp
  also have "\<dots> = lang (subst (Atom x) \<sigma>) @@ ( lang (subst (w2rexp xs) \<sigma>) @@ lang (subst (w2rexp ys) \<sigma>) )" by(simp only: Cons)
  also have "\<dots> = lang (Times (subst (Atom x) \<sigma>) (subst (w2rexp xs) \<sigma>)) @@ lang (subst (w2rexp ys) \<sigma>) " 
            apply(simp del: subst.simps) by(rule conc_assoc[symmetric])
  also have "\<dots> = lang (subst (Times (Atom x) (w2rexp xs)) \<sigma>) @@ lang (subst (w2rexp ys) \<sigma>)" by simp
  also have "\<dots> = lang (subst (w2rexp (x # xs)) \<sigma>) @@ lang (subst (w2rexp ys) \<sigma>)" by simp
  finally show ?case .
qed simp

fun substW :: "nat list \<Rightarrow> (nat \<Rightarrow> nat rexp option) \<Rightarrow> nat rexp" where
  "substW as \<sigma> = subst (w2rexp as) \<sigma>"

fun substL :: "nat lang \<Rightarrow> (nat \<Rightarrow> nat rexp option) \<Rightarrow> nat rexp set" where
  "substL S \<sigma> = {substW a \<sigma>|a. a \<in> S}"

fun L :: "nat rexp set \<Rightarrow> nat lang" where
  "L S = (\<Union>r\<in>S. lang r)"

lemma L_mono: "S1 \<subseteq> S2 \<Longrightarrow> L S1 \<subseteq> L S2"
apply(simp) by blast

definition concS :: "'b rexp set \<Rightarrow> 'b rexp set \<Rightarrow> 'b rexp set" where
  "concS S1 S2 = {Times a b|a b. a\<in>S1 \<and> b\<in>S2}"

lemma substL_conc: "L (substL (L1 @@ L2) \<sigma>) = L (concS (substL L1 \<sigma>) (substL L2 \<sigma>))"
apply(simp add: concS_def conc_def)
apply(auto)
proof (goal_cases)
  case (1 x xs ys)
  show ?case
    apply(rule exI[where x="Times (subst (w2rexp xs) \<sigma>) (subst (w2rexp ys) \<sigma>)"])
    apply(simp)
    apply(safe)
     apply(rule exI[where x="xs"]) apply(simp add: 1(2))
     apply(rule exI[where x="ys"]) apply(simp add: 1(3))
     using 1(1) subst_w2rexp by auto
next
  case (2 x xs ys)
  show ?case
    apply(rule exI[where x="subst (w2rexp (xs @ ys)) \<sigma>"])
    apply(safe)
      apply(rule exI[where x="xs@ys"]) apply(simp)
        apply(rule exI[where x="xs"])
        apply(rule exI[where x="ys"]) using 2(2,3) apply(simp)
      using 2(1) subst_w2rexp by(auto)
qed

lemma L_conc: "L(concS M1 M2) = (L M1) @@ (L M2)"
proof -
  have "L(concS M1 M2) = (\<Union>x\<in>{Times a b |a b. a \<in> M1 \<and> b \<in> M2}. lang x)" unfolding concS_def by(simp)
  also have "\<dots> = (\<Union>{lang (Times a b) |a b. a \<in> M1 \<and> b \<in> M2} )" by blast
  also have "\<dots> = (\<Union>{lang a @@ lang b |a b. a \<in> M1 \<and> b \<in> M2} )" by simp
  also have "\<dots> = (\<Union>{{xs@ys | xs ys. xs \<in> lang a & ys \<in> lang b} |a b. a \<in> M1 \<and> b \<in> M2} )" unfolding conc_def by simp
  also have "\<dots> = {xs@ys | xs ys. xs\<in> (\<Union>r\<in>M1. lang r) \<and> ys \<in> (\<Union>r\<in>M2. lang r) }" by blast
  also have "\<dots> = {xs@ys | xs ys. xs\<in> L(M1) \<and> ys \<in> L(M2) }" by simp
  also have "\<dots> = (L M1) @@ (L M2)" unfolding conc_def by simp
  finally show ?thesis .
qed
  
lemma "L(M1 \<union> M2) = (L M1) \<union> (L M2)"
by simp

fun verund :: "'b rexp list \<Rightarrow> 'b rexp" where
  "verund [] = Zero"
| "verund [r] = r"
| "verund (r#rs) = Plus r (verund rs)"

lemma lang_verund: "r \<in> L (set rs) = (r \<in> lang (verund rs))"
apply(induct rs)
  apply(simp)
  apply(case_tac rs) by auto

lemma obtainit: 
  assumes "r \<in> lang (verund rs)"
  shows "\<exists>x\<in>(set (rs::nat rexp list)). r \<in> lang x"
proof -
  from assms have "r \<in> L (set rs)" by(simp only: lang_verund)
  then show ?thesis by(auto)
qed



lemma lang_verund4: "L (set rs) = lang (verund rs)"
apply(induct rs)
  apply(simp)
  apply(case_tac rs) by auto

lemma lang_verund1: "r \<in> L (set rs) \<Longrightarrow> r \<in> lang (verund rs)"
apply(induct rs)
  apply(simp)
  apply(case_tac rs) by auto
lemma lang_verund2: "r \<in> lang (verund rs) \<Longrightarrow> r \<in> L (set rs)"
apply(induct rs)
  apply(simp)
  apply(case_tac rs) by auto

definition starS :: "'b rexp set \<Rightarrow> 'b rexp set" where
  "starS S = {Star (verund xs)|xs. set xs \<subseteq> S}"

lemma "[] \<in> L (starS S)"
unfolding starS_def apply(simp)
  apply(rule exI[where x="Star(verund [])"])
  apply(simp)
    apply(rule exI[where x="[]"])
    by (simp)

lemma power_mono: "L1 \<subseteq> L2 \<Longrightarrow> (L1::'a lang) ^^ n \<subseteq> L2 ^^ n"
apply(auto) apply(induct n) by(auto simp: conc_def)

lemma star_mono: "L1 \<subseteq> L2 \<Longrightarrow> star L1 \<subseteq> star L2"
  apply (simp add: star_def)
  apply (rule UN_mono)
  apply (auto simp: power_mono)
  done

lemma Lstar: "L(starS M) = star ( L(M) )"
unfolding starS_def apply(auto)
proof (goal_cases)
  case (1 x xs)
  from 1(2) have "L (set xs) \<subseteq> L (M)" by(rule L_mono)
  then have a: "star (L (set xs)) \<subseteq> star (L (M))" by (rule star_mono)
  from 1(1) obtain n where "x \<in> (lang (verund xs)) ^^ n" unfolding star_def by(auto)
  thm lang_verund4
  then have "x \<in> (L (set xs)) ^^ n" by(simp only: lang_verund4)
  then have "x \<in> star (L (set xs))" unfolding star_def by auto
  with a have "x \<in> star (L (M))" by auto
  then show "x \<in> star (\<Union>x\<in>M. lang x)" unfolding starS_def by auto
next
  case (2 x)
  then obtain n where "x \<in> (\<Union>x\<in>M. lang x) ^^ n" unfolding star_def by auto
  then show ?case
  proof (induct n arbitrary: x)
    case 0
    then have t: "x=[]" by(simp)
    show ?case
      apply(rule exI[where x="Star Zero"])
      apply(auto simp: t) apply(rule exI[where x="[]"]) by(simp)
  next
    case (Suc n)
    from Suc(2) have t: "x \<in> (\<Union>a\<in>M. lang a) @@ (\<Union>a\<in>M. lang a) ^^ n" by (simp)
    then obtain A B where x: "x = A @ B" and A: "A \<in> (\<Union>a\<in>M. lang a)" and B: "B \<in> (\<Union>a\<in>M. lang a) ^^ n" by(auto simp: conc_def)
    then obtain m where am: "A \<in> lang m" and mM: "m\<in>M" by(auto)
    from Suc(1)[OF B] obtain b bs where "b = Star (verund bs)" and bsM: "set bs \<subseteq> M" "B \<in> lang b" by auto
    then have Bin:  "B \<in> lang (Star (verund bs))" by simp
    let ?c = "Star (verund (m#bs))"

    have ac: "lang m \<subseteq> lang (Star (verund (m # bs)))" 
      apply(cases bs) by(auto)
    have ad: "(lang (Star (verund bs))) \<subseteq> lang (Star (verund (m # bs)))"
      apply (simp add: star_def)
      apply (rule UN_mono)
      apply simp_all
      proof -
        fix n
        have t: "(lang (verund bs) ^^ n) \<subseteq> (lang m \<union> lang (verund bs)) ^^ n"
          by (rule power_mono) simp
        then show "lang (verund bs) ^^ n
          \<subseteq> lang (verund (m # bs)) ^^ n" by (cases bs) simp_all
      qed

    from Bin am mM x have "x \<in> lang m @@ (lang (Star (verund bs)))" by auto
    then have " x \<in> lang (Star (verund (m # bs))) @@ lang (Star (verund (m # bs)))" using ac ad by blast
    then have x_in: "x \<in> lang (Star (verund (m # bs)))" by (auto)

    
    show ?case
      apply(rule exI[where x="?c"])
      apply(safe)
        apply(rule exI[where x="m#bs"]) apply(simp add: bsM mM)
        by(fact x_in)
  qed
qed        

lemma substL_star: "L (substL (star L1) \<sigma>) = L (starS (substL L1 \<sigma>))"
apply (simp add: concS_def conc_def starS_def star_def)
apply auto unfolding star_def
proof -
  fix x a n
  assume "x \<in> lang (subst (w2rexp a) \<sigma>)"
  moreover assume "a \<in> L1 ^^ n"
  ultimately show "\<exists>xa. (\<exists>xs. xa = Star (verund xs) \<and> set xs
    \<subseteq> {subst (w2rexp a) \<sigma> | a. a \<in> L1}) \<and> x \<in> lang xa"
  proof(induct n arbitrary: x a)
    case 0
    then have "a=[]" by auto
    with 0 show ?case apply(simp)
    apply(rule exI[where x="Star (Zero)"])
    apply(simp)
      apply(rule exI[where x="[]"])
      by(simp)
  next
    case (Suc n)
    then have a1: "a \<in> L1 @@ L1 ^^ n" by auto
    then obtain A B where a2: "a = A @ B" and A: "A \<in> L1" and B: "B \<in> L1 ^^ n" by auto

    thm subst_w2rexp
    from Suc(2) have "x \<in> lang (subst (w2rexp A) \<sigma>) @@ lang (subst (w2rexp B) \<sigma>)" unfolding a2
          by(simp only: subst_w2rexp)
    then obtain x1 x2 where x: "x = x1@x2" and x1: "x1 \<in> lang (subst (w2rexp A) \<sigma>)"
                    and  x2: "x2 \<in> lang (subst (w2rexp B) \<sigma>)" by auto
    from Suc(1)[OF x2 B] obtain R li where
          R: "R = Star (verund li)" and li: "set li \<subseteq> {subst (w2rexp a) \<sigma> |a. a \<in> L1}"
              and x2R: "x2 \<in> lang R" by auto


    show ?case
      apply(rule exI[where x="Star (verund ((subst (w2rexp A) \<sigma>)#li))"])
      apply(simp)
      apply(safe)
        apply(rule exI[where x="((subst (w2rexp A) \<sigma>)#li)"])
        apply(simp add: li) 
          apply(rule exI[where x="A"]) apply(simp add: A)
        unfolding x
        proof (goal_cases)
          case 1
          let ?L = "(lang (subst (w2rexp A) \<sigma>) \<union> lang (verund li))"
          have t1: "x1 \<in> ?L" using x1 star_mono by blast
          have t2: "x2 \<in> star ?L" using x2R R star_mono apply(simp) by blast
          have "x1 @ x2 \<in> (?L @@ star ?L)" using t1 t2 by auto
          then show ?case 
          apply(cases li) by(auto)
        qed
    qed
next
  fix x and xs :: "nat rexp list"
  assume "x \<in> (\<Union>n. lang (verund xs) ^^ n)"
  then obtain n where "x \<in> lang (verund xs) ^^ n" by auto
  moreover assume "set xs \<subseteq> {subst (w2rexp a) \<sigma> |a. a \<in> L1}"
  ultimately show "\<exists>xa. (\<exists>a. xa = subst (w2rexp a) \<sigma> \<and>
    (\<exists>n. a \<in> L1 ^^ n)) \<and> x \<in> lang xa"
  proof (induct n arbitrary: x)
    case 0
    then have xe: "x=[]" by auto
    show ?case
      apply(rule exI[where x="One"])
      apply(simp add: xe)
        apply(rule exI[where x="[]"])
        apply(simp)
          apply(rule exI[where x="0"])
          by(simp)
  next
    case (Suc n)
    then have "x \<in> lang (verund xs) @@ (lang (verund xs) ^^ n)" by auto
    then obtain x1 x2 where x: "x=x1@x2" and x1: "x1\<in>lang (verund xs)"
                      and x2: "x2 \<in> (lang (verund xs) ^^ n)" by auto
    from obtainit [OF x1] obtain el
      where "el \<in> set xs" and "x1 \<in> lang el" by auto
    with Suc.prems obtain elem
      where x1elem: "x1 \<in> lang (subst (w2rexp elem) \<sigma>)"
      and elemL1: "elem \<in> L1" by auto
    from Suc.hyps [OF x2 Suc.prems(2)] obtain R word n where
         R: "R = subst (w2rexp word) \<sigma>" and word: "word \<in> L1 ^^ n" and x2: "x2 \<in> lang R" by auto
    
                      
    show ?case
      apply(rule exI[where x="subst (w2rexp (elem@word)) \<sigma>"])
      apply(safe)
        apply(rule exI[where x="elem@word"])
        apply(simp)
          apply(rule exI[where x="Suc n"])
          proof (goal_cases)
            case 1
            have "elem \<in> L1" by(fact elemL1)
            with word
            show "elem @ word \<in> L1 ^^ Suc n" by simp
          next
            case 2
            have "x1 \<in> lang (subst (w2rexp elem) \<sigma>)" by(fact x1elem)
            with x2[unfolded R] show ?case unfolding x apply(simp only: subst_w2rexp) by blast
          qed
  qed
qed

lemma substituitionslemma: 
  fixes E :: "nat rexp"
  shows "L (substL ( lang(E) ) \<sigma>) = lang (subst E \<sigma>)"
proof (induct E)
  case (Star e)
  have "L (substL (lang (Star e)) \<sigma>) = L (substL (star (lang e)) \<sigma>)" by auto
  also have "\<dots> = L (starS (substL (lang e) \<sigma>))" by(simp only: substL_star)
  also have "\<dots> = star ( L (substL (lang e) \<sigma>))" by(simp only: Lstar)
  also have "\<dots> = star (lang (subst e \<sigma>))" by(simp only: Star)
  also have "\<dots> = lang ((subst (Star e) \<sigma>))" by auto
  finally show ?case .
next
  case (Plus e1 e2)
  have "L (substL (lang (Plus e1 e2)) \<sigma>) = L (substL (lang e1 \<union> lang e2) \<sigma>)" by simp
  also have "\<dots> =  L ( substL (lang e1) \<sigma> \<union> substL (lang e2) \<sigma>)" by auto
  also have "\<dots> = L (substL (lang e1) \<sigma>) \<union> L (substL (lang e2) \<sigma>)" by auto
  also have "\<dots> = lang (subst e1 \<sigma>) \<union> lang (subst e2 \<sigma>)" by(simp only: Plus)
  also have "\<dots> = lang (subst (Plus e1 e2) \<sigma>)" by auto
  finally show ?case .
next
  case (Times e1 e2)
  have "L (substL (lang (Times e1 e2)) \<sigma>) = L (substL (lang e1 @@ lang e2) \<sigma>)" by(simp)
  also have "\<dots> =  L (concS (substL (lang e1) \<sigma>) (substL (lang e2) \<sigma>))" by(simp only: substL_conc)
  thm L_conc
  also have "\<dots> = L (substL (lang e1) \<sigma>) @@ L (substL (lang e2) \<sigma>)" by(simp only: L_conc)
  also have "\<dots> = lang (subst e1 \<sigma>) @@ lang (subst e2 \<sigma>)" by(simp only: Times)
  also have "\<dots> = lang (Times (subst e1 \<sigma>) (subst e2 \<sigma>))" by auto
  also have "\<dots> = lang (subst (Times e1 e2) \<sigma>)" by auto
  finally show ?case .
qed simp_all


corollary lift: "lang e1 = lang e2 \<Longrightarrow> lang (subst e1 \<sigma>) = lang (subst e2 \<sigma>)"
proof -
  assume eq: "lang e1 = lang e2"
  thm substituitionslemma
  have "lang (subst e1 \<sigma>) = L (substL (lang e1) \<sigma>)" by(simp only: substituitionslemma)
  also have "\<dots> = L (substL (lang e2) \<sigma>)" using eq by simp
  also have "\<dots> = lang (subst e2 \<sigma>)" by(simp only: substituitionslemma)
  finally show ?thesis .
qed


subsection \<open>Examples\<close>

lemma "lang (Plus (Atom (x::nat)) (Atom x))  = lang (Atom x)"
proof -
  let ?\<sigma> = "(\<lambda>i. (if i=0 then Some (Atom x) else None))"
  let ?e1 = "Plus (Atom 1) (Atom 1)"
  let ?e2 = "Atom 1"
  have "lang (Plus (Atom x) (Atom x)) = lang (subst ?e1 ?\<sigma>)" by (simp)
  thm soundness
  also have "\<dots> = lang (subst ?e2 ?\<sigma>)"
        apply(rule lift)
        apply(rule soundness)
        by eval
  also have "\<dots> = lang (Atom x)" by auto
  finally show ?thesis .
qed


fun seq :: "'a rexp list \<Rightarrow> 'a rexp" where
"seq [] = One" |
"seq [r] = r" |
"seq (r#rs) = Times r (seq rs)"


abbreviation question where "question x == Plus x One" 

definition "L_4cases (x::nat) y=
    verund [seq[question (Atom x),(Atom y), (Atom y)],
            seq[question (Atom x),(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom y),(Atom y)],
            seq[question (Atom x),(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom x)],
            seq[(Atom x),(Atom x)] ]"

definition "L_A x y = seq[question (Atom x),(Atom y), (Atom y)]"
definition "L_B x y = seq[question (Atom x),(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom y),(Atom y)]"
definition "L_C x y = seq[question (Atom x),(Atom y),(Atom x),Star(Times (Atom y)(Atom x)),(Atom x)]"
definition "L_D x y = seq[(Atom x),(Atom x)]"

lemma "L_4cases x y = verund [L_A x y, L_B x y, L_C x y, L_D x y]"
unfolding L_A_def L_B_def L_C_def L_D_def L_4cases_def by auto


definition "L_lasthasxx x y = (Plus (seq[question (Atom x), Star(Times (Atom y)(Atom x)),(Atom y),(Atom y)])
       (seq[question (Atom y), Star(Times(Atom x) (Atom y)),(Atom x),(Atom x)]))"



lemma lastxx_com: "lang (L_lasthasxx (x::nat) y) = lang (L_lasthasxx y x)" (is "lang ?A = lang ?B")
proof -
  let ?\<sigma> = "(\<lambda>i. (if i=0 then Some (Atom x) else (if i=1 then Some (Atom y) else None)))"
  
  let ?e1 = "Plus (seq[Plus (Atom 1) One, Star(Times (Atom 3) (Atom 1)),(Atom 3),(Atom 3)])
       (seq[Plus (Atom 3) One, Star(Times (Atom 1) (Atom 3)),(Atom 1),(Atom 1)])"
  let ?e2 = "Plus (seq[Plus (Atom 3) One, Star(Times (Atom 1) (Atom 3)),(Atom 1),(Atom 1)])
           (seq[Plus (Atom 1) One, Star(Times (Atom 3) (Atom 1)),(Atom 3),(Atom 3)])"
  have "lang ?A = lang (subst ?e1 ?\<sigma>)" by(simp add: L_lasthasxx_def)
  thm soundness
  also have "\<dots> = lang (subst ?e2 ?\<sigma>)"
        apply(rule lift)
        apply(rule soundness)
        by eval
  also have "\<dots> = lang ?B" by (simp add: L_lasthasxx_def)
  finally show ?thesis .
qed


lemma lastxx_is_4cases: "lang (L_4cases x y) = lang (L_lasthasxx x y)" (is "lang ?A = lang ?B")
proof -
  let ?\<sigma> = "(\<lambda>i. (if i=0 then Some (Atom x) else (if i=1 then Some (Atom y) else None)))"
  
  let ?e1 = "(Plus (seq[Plus (Atom 1) One,(Atom 3), (Atom 3)])
            (Plus (seq[Plus (Atom 1) One,(Atom 3),(Atom 1),Star(Times (Atom 3) (Atom 1)),(Atom 3),(Atom 3)])
            (Plus (seq[Plus (Atom 1) One,(Atom 3),(Atom 1),Star(Times (Atom 3) (Atom 1)),(Atom 1)])
                  (seq[(Atom 1),(Atom 1)]))))"
  let ?e2 = "Plus (seq[Plus (Atom 1) One, Star(Times (Atom 3) (Atom 1)),(Atom 3),(Atom 3)])
       (seq[Plus (Atom 3) One, Star(Times (Atom 1) (Atom 3)),(Atom 1),(Atom 1)])"
  have "lang ?A = lang (subst ?e1 ?\<sigma>)" by (simp add: L_4cases_def)
  thm soundness
  also have "\<dots> = lang (subst ?e2 ?\<sigma>)"
        apply(rule lift)
        apply(rule soundness)
        by eval
  also have "\<dots> = lang ?B" by (simp add: L_lasthasxx_def)
  finally show ?thesis .
qed

definition "myUNIV x y = Star (Plus (Atom x) (Atom y))"


lemma myUNIV_alle: "lang (myUNIV x y) = {xs. set xs \<subseteq> {x,y}}"
proof -
  have "star {[y], [x]}  = {concat ws |ws. set ws \<subseteq> {[y], [x]}}" by(simp only: star_conv_concat)
  also have "\<dots> = {xs. set xs \<subseteq> {x, y}}" apply(auto) apply(cases "x=y") apply(simp) 
        apply(case_tac ws)
          apply(simp)
          apply(auto)
        proof (goal_cases)
          case (1 as)
          then show ?case
            proof (induct as)
              case (Cons a as)
              then have as: "set as \<subseteq> {x,y}" and axy: "a \<in> {x,y}" by auto
              from Cons(1)[OF as] obtain ws where asco: "as = concat ws" and ws: "set ws \<subseteq> {[y],[x]}" by auto
              show ?case
                apply(rule exI[where x="[a]#ws"])
                using axy by(auto simp add: asco ws)
            qed (rule exI[where x="[]"], simp)
          qed
   finally show ?thesis by(simp add: myUNIV_def)
qed

definition "nodouble x y = (Plus
                   (seq[question (Atom x), Star(Times(Atom y)(Atom x)),(Atom y)])
                   (seq[question (Atom y), Star(Times(Atom x) (Atom y)),(Atom x)]))"

lemma myUNIV_char: "lang (myUNIV (x::nat) y) = lang (Times (Star (L_lasthasxx x y)) (Plus One (nodouble x y)))" (is "lang ?A = lang ?B")
proof -
  let ?\<sigma> = "(\<lambda>i. (if i=0 then Some (Atom x) else (if i=1 then Some (Atom y) else None)))"
  
  let ?e1 = "Star (Plus (Atom 1) (Atom 3))"
  let ?e2 = "(Times (Star (Plus (seq [Plus (Atom 1) One, Star  (Times (Atom 3) (Atom 1)), Atom 3, Atom 3])
           (seq [Plus (Atom 3) One, Star (Times (Atom 1) (Atom 3)), Atom 1, Atom 1])))
       (Plus One
         (Plus
           (seq
             [Plus (Atom 1)
               One,
              Star
               (Times (Atom 3)
 (Atom 1)),
              Atom 3])
           (seq
             [Plus (Atom 3)
               One,
              Star
               (Times (Atom 1)
 (Atom 3)),
              Atom 1]))))"
  have "lang ?A = lang (subst ?e1 ?\<sigma>)" by(simp add: myUNIV_def)
  thm soundness
  also have "\<dots> = lang (subst ?e2 ?\<sigma>)"
        apply(rule lift)
        apply(rule soundness)
        by eval
  also have "\<dots> = lang ?B" by (simp add: L_lasthasxx_def nodouble_def)
  finally show ?thesis .
qed


definition "mycasexxy x y = Plus (seq[Star (Plus (Atom x) (Atom y)), Atom x, Atom x, Atom y])
                (seq[Star (Plus (Atom x) (Atom y)), Atom y, Atom y, Atom x])"
definition "mycasexyx x y = Plus (seq[Star (Plus (Atom x) (Atom y)), Atom x, Atom y, Atom x])
                (seq[Star (Plus (Atom x) (Atom y)), Atom y, Atom x, Atom y])"
definition "mycasexx x y = Plus (seq[Star (Plus (Atom x) (Atom y)), Atom x,  Atom x])
                (seq[Star (Plus (Atom x) (Atom y)), Atom y, Atom y])"
definition "mycasexy x y = Plus (seq[Atom x,  Atom y]) (seq[Atom y, Atom x])"
definition "mycasex x y = Plus (Atom y) (Atom x)"



definition "mycases x y = Plus
                   (mycasexxy x y)
              (Plus (mycasexyx x y)
              (Plus (mycasexx x y) 
                    (Plus (mycasexy x y) (Plus (mycasex x y) (One)))))"
 
lemma mycases_char: "lang (myUNIV (x::nat) y) = lang (mycases x y)" (is "lang ?A = lang ?B")
proof -
  let ?\<sigma> = "(\<lambda>i. (if i=0 then Some (Atom x) else (if i=1 then Some (Atom y) else None)))"
  
  let ?e1 = "Star (Plus (Atom 1) (Atom 3))"
  let ?e2 = "Plus (Plus (seq [Star (Plus (Atom 1) (Atom 3)), Atom 1, Atom 1, Atom 3])
           (seq [Star (Plus (Atom 1) (Atom 3)), Atom 3, Atom 3, Atom 1]))
     (Plus (Plus (seq [Star (Plus (Atom 1) (Atom 3)), Atom 1, Atom 3, Atom 1])
             (seq [Star (Plus (Atom 1) (Atom 3)), Atom 3, Atom 1, Atom 3]))
       (Plus (Plus (seq [Star (Plus (Atom 1) (Atom 3)), Atom 1, Atom 1])
               (seq [Star (Plus (Atom 1) (Atom 3)), Atom 3, Atom 3]))
         (Plus (Plus (seq [Atom 1, Atom 3]) (seq [Atom 3, Atom 1])) (Plus (Plus (Atom 3) (Atom 1)) One))))"

  have "lang ?A = lang (subst ?e1 ?\<sigma>)" by(simp add: myUNIV_def)
  thm soundness
  also have "\<dots> = lang (subst ?e2 ?\<sigma>)"
        apply(rule lift)
        apply(rule soundness)
        by eval
  also have "\<dots> = lang ?B" by (simp add:  mycases_def mycasexxy_def mycasexyx_def 
                                          mycasexx_def mycasex_def mycasexy_def)
  finally show ?thesis .
qed       
 

end
