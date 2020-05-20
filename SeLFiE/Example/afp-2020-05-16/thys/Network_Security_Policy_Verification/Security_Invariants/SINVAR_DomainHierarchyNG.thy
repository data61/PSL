theory SINVAR_DomainHierarchyNG
imports "../TopoS_Helper"
  "HOL-Lattice.CompleteLattice" (* markarius lattice *)
begin


subsection\<open>SecurityInvariant DomainHierarchyNG\<close>

subsubsection \<open>Datatype Domain Hierarchy\<close>

  text\<open>A fully qualified domain name for an entity in a tree-like hierarchy\<close>
    datatype domainNameDept =  Dept "string" domainNameDept (infixr "--" 65) |
                               Leaf \<comment> \<open>leaf of the tree, end of all domainNames\<close>
    
    text \<open>Example: the CoffeeMachine of I8\<close>
    value "''i8''--''CoffeeMachine''--Leaf"

  text\<open>A tree strucuture to represent the general hierarchy, i.e. possible domainNameDepts\<close>
    datatype domainTree = Department 
        "string"  \<comment> \<open>division\<close>
        "domainTree list"  \<comment> \<open>sub divisions\<close>

  text\<open>one step in tree to find matching department\<close>
    fun hierarchy_next :: "domainTree list \<Rightarrow> domainNameDept \<Rightarrow> domainTree option" where
      "hierarchy_next [] _ = None" | 
      "hierarchy_next (s#ss) Leaf = None" | 
      "hierarchy_next ((Department d ds)#ss) (Dept n ns) = (if d=n then Some (Department d ds) else hierarchy_next ss (Dept n ns))"

    text \<open>Examples:\<close>
    lemma "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        (''i8''--Leaf)
        =
        Some (Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []])" by eval
    lemma "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        (''i8''--''whatsoever''--Leaf)
        =
        Some (Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []])" by eval
    lemma "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        Leaf
        = None" by eval
    lemma "hierarchy_next [Department ''i20'' [], Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []]] 
        (''i0''--Leaf)
        = None" by eval

  text \<open>Does a given @{typ domainNameDept} match the specified tree structure?\<close>
    fun valid_hierarchy_pos :: "domainTree \<Rightarrow> domainNameDept \<Rightarrow> bool" where
      "valid_hierarchy_pos (Department d ds) Leaf = True" |
      "valid_hierarchy_pos (Department d ds) (Dept n Leaf) = (d=n)" |
      "valid_hierarchy_pos (Department d ds) (Dept n ns) = (n=d \<and> 
        (case hierarchy_next ds ns of 
          None \<Rightarrow> False |
          Some t \<Rightarrow> valid_hierarchy_pos t ns))"


     text \<open>Examples:\<close>
     lemma "valid_hierarchy_pos (Department ''TUM'' []) Leaf" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' []) Leaf" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' []) (''TUM''--Leaf)" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' []) (''TUM''--''facilityManagement''--Leaf) = False" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' []) (''LMU''--Leaf) = False" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], (Department ''i20'' [])])  (''TUM''--Leaf)" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []])  (''TUM''--''i8''--Leaf)" by eval
     lemma "valid_hierarchy_pos 
        (Department ''TUM'' [
           Department ''i8'' [
            Department ''CoffeeMachine'' [],
            Department ''TeaMachine'' []
           ], 
           Department ''i20'' []
        ]) 
        (''TUM''--''i8''--''CoffeeMachine''--Leaf)" by eval
     lemma "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [Department ''CoffeeMachine'' [], Department ''TeaMachine'' []], Department ''i20'' []]) 
        (''TUM''--''i8''--''CleanKitchen''--Leaf) = False" by eval

     (*end tree*)
     
  
  instantiation domainNameDept :: order
  begin
    print_context
    
    fun less_eq_domainNameDept :: "domainNameDept \<Rightarrow> domainNameDept \<Rightarrow> bool" where
      "Leaf \<le> (Dept _ _) = False" |
      "(Dept _ _) \<le> Leaf = True" |
      "Leaf \<le> Leaf = True" |
      "(Dept n1 n1s) \<le> (Dept n2 n2s) = (n1=n2 \<and> n1s \<le> n2s)"
    
    fun less_domainNameDept :: "domainNameDept \<Rightarrow> domainNameDept \<Rightarrow> bool" where
      "Leaf < Leaf = False" |
      "Leaf < (Dept _ _) = False" |
      "(Dept _ _) < Leaf = True" |
      "(Dept n1 n1s) < (Dept n2 n2s) = (n1=n2 \<and> n1s < n2s)"
    
    lemma Leaf_Top: "a \<le> Leaf"
      apply(case_tac a)
      by(simp_all)
  
    lemma Leaf_Top_Unique: "Leaf \<le> a = (a = Leaf)"
      apply(case_tac a)
      by(simp_all)
  
    lemma no_Bot: "n1 \<noteq> n2 \<Longrightarrow> z \<le> n1 -- n1s \<Longrightarrow> z \<le> n2 -- n2s \<Longrightarrow> False"
      apply(case_tac z)
      by(simp_all)
  
    lemma uncomparable_sup_is_Top: "n1 \<noteq> n2 \<Longrightarrow> n1 -- x \<le> z \<Longrightarrow> n2 -- y \<le> z \<Longrightarrow> z = Leaf"
      apply(case_tac z)
      by(simp_all)

   lemma common_inf_imp_comparable: "(z::domainNameDept) \<le> a \<Longrightarrow> z \<le> b \<Longrightarrow> a \<le> b \<or> b \<le> a"
      apply(induction z arbitrary: a b)
       apply(rename_tac zn zdpt a b)
       apply(simp_all add: Leaf_Top_Unique)
      apply(case_tac a)
       apply(rename_tac an adpt)
       apply(simp_all add: Leaf_Top)
      apply(case_tac b)
       apply(rename_tac bn bdpt)
       apply(simp_all add: Leaf_Top)
      done
  
    lemma prepend_domain: "a \<le> b \<Longrightarrow> x--a \<le> x--b"
      by(simp)
    lemma unfold_dmain_leq: "y \<le> zn -- zns \<Longrightarrow> \<exists>yns. y = zn -- yns \<and> yns \<le> zns"
      proof -
        assume a1: "y \<le> zn -- zns"
        obtain sk\<^sub>3\<^sub>0 :: "domainNameDept \<Rightarrow> char list" and sk\<^sub>3\<^sub>1 :: "domainNameDept \<Rightarrow> domainNameDept" where "\<forall>x\<^sub>0. sk\<^sub>3\<^sub>0 x\<^sub>0 -- sk\<^sub>3\<^sub>1 x\<^sub>0 = x\<^sub>0 \<or> Leaf = x\<^sub>0"
          by (metis domainNameDept.exhaust)
        thus "\<exists>yns. y = zn -- yns \<and> yns \<le> zns"
          using a1 by (metis less_eq_domainNameDept.simps(1) less_eq_domainNameDept.simps(4))
      qed
  
    lemma less_eq_refl: 
      fixes x :: domainNameDept
      shows "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
      proof -
      have "x \<le> y \<longrightarrow> y \<le> z \<longrightarrow> x \<le> z" (*induction over prems and conclusion*)
        proof(induction z arbitrary:x y)
        case Leaf
          have "x \<le> Leaf" using Leaf_Top by simp
          thus ?case by simp
        next
        case (Dept zn zns)
          show ?case proof(clarify)
            assume a1: "x \<le> y" and a2: "y \<le> zn--zns"
            from unfold_dmain_leq[OF a2] obtain yns where y1: "y = zn--yns" and y2: "yns \<le> zns" by auto
            from unfold_dmain_leq this a1 obtain xns where x1: "x = zn -- xns" and x2: "xns \<le> yns" by blast
            from Dept y2 x2 have "xns \<le> zns" by simp
            from this x1 show "x \<le> zn--zns" by simp
          qed
        qed
      thus "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" by simp
      qed
  
    instance
      proof
        fix x y ::domainNameDept
        show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
          apply(induction rule: less_domainNameDept.induct)
           apply(simp_all)
          by blast
      next
        fix x::domainNameDept
        show "x \<le> x"
          using[[show_types]] apply(induction x)
          by simp_all
      next
        fix x y z :: domainNameDept
        show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z " apply (rule less_eq_refl) by simp_all
      next
        fix x y ::domainNameDept
        show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
          apply(induction rule: less_domainNameDept.induct)
             by(simp_all)
    qed
  end

  instantiation domainNameDept :: Orderings.top
  begin
    definition top_domainNameDept where "Orderings.top \<equiv> Leaf"
    instance
      by intro_classes
  end

    lemma "(''TUM''--''BLUBB''--Leaf) \<le> (''TUM''--Leaf)" by eval

    lemma "(''TUM''--''i8''--Leaf) \<le> (''TUM''--Leaf)" by eval
    lemma "\<not> (''TUM''--Leaf) \<le> (''TUM''--''i8''--Leaf)"  by eval
    lemma "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--''i8''--Leaf)" by eval
    
    lemma "(''TUM''--Leaf) \<le> Leaf" by eval
    lemma "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (Leaf)" by eval

    lemma "\<not> Leaf \<le> (''TUM''--Leaf)" by eval
    lemma "valid_hierarchy_pos (Department ''TUM'' [Department ''i8'' [], Department ''i20'' []]) (''TUM''--Leaf)" by eval

    lemma "\<not> (''TUM''--''BLUBB''--Leaf) \<le> (''X''--''TUM''--''BLUBB''--Leaf)" by eval

    lemma "(''TUM''--''i8''--''CoffeeMachine''--Leaf) \<le> (''TUM''--''i8''--Leaf)" by eval
    lemma "(''TUM''--''i8''--Leaf) \<le> (''TUM''--''i8''--Leaf)" by eval
    lemma "(''TUM''--''i8''--''CoffeeMachine''--Leaf) \<le> (''TUM''--Leaf)" by eval
    lemma "(''TUM''--''i8''--''CoffeeMachine''--Leaf) \<le> (Leaf)" by eval
    lemma "\<not> (''TUM''--''i8''--Leaf) \<le> (''TUM''--''i20''--Leaf)" by eval
    lemma "\<not> (''TUM''--''i20''--Leaf) \<le> (''TUM''--''i8''--Leaf)" by eval



  subsubsection \<open>Adding Chop\<close>
  text\<open>by putting entities higher in the hierarchy.\<close>
    fun domainNameDeptChopOne :: "domainNameDept \<Rightarrow> domainNameDept" where
      "domainNameDeptChopOne Leaf = Leaf" |
      "domainNameDeptChopOne (name--Leaf) = Leaf" |
      "domainNameDeptChopOne (name--dpt) = name--(domainNameDeptChopOne dpt)"
    
    
    lemma "domainNameDeptChopOne (''i8''--''CoffeeMachine''--Leaf) = ''i8'' -- Leaf" by eval
    lemma "domainNameDeptChopOne (''i8''--''CoffeeMachine''--''CoffeeSlave''--Leaf) = ''i8'' -- ''CoffeeMachine'' -- Leaf" by eval
    lemma "domainNameDeptChopOne Leaf = Leaf" by(fact domainNameDeptChopOne.simps(1))
    
    theorem chopOne_not_decrease: "dn \<le> domainNameDeptChopOne dn"
      apply(induction dn)
       apply(rename_tac name dpt)
       apply(drule_tac x="name" in prepend_domain)
       apply(case_tac dpt)
        apply simp_all
    done
    
    lemma chopOneContinue: "dpt \<noteq> Leaf \<Longrightarrow> domainNameDeptChopOne (name -- dpt) = name -- domainNameDeptChopOne (dpt)"
    apply(case_tac dpt)
     by simp_all
    
    fun domainNameChop :: "domainNameDept \<Rightarrow> nat \<Rightarrow> domainNameDept" where
      "domainNameChop Leaf _ = Leaf" |
      "domainNameChop namedpt 0 = namedpt" |
      "domainNameChop namedpt (Suc n) = domainNameChop (domainNameDeptChopOne namedpt) n"
    
    lemma "domainNameChop (''i8''--''CoffeeMachine''--Leaf) 2 = Leaf" by eval
    lemma "domainNameChop (''i8''--''CoffeeMachine''--''CoffeeSlave''--Leaf) 2 = ''i8''--Leaf" by eval
    lemma "domainNameChop (''i8''--Leaf) 0 = ''i8''--Leaf" by eval
    lemma "domainNameChop (Leaf) 8 = Leaf" by eval
    
    
    lemma chop0[simp]: "domainNameChop dn 0 = dn"
     apply(case_tac dn)
      by simp_all
    
    
    lemma "(domainNameDeptChopOne^^2) (''d1''--''d2''--''d3''--Leaf) = ''d1''--Leaf" by eval
    
    text \<open>domainNameChop is equal to applying n times chop one\<close>
    lemma domainNameChopFunApply: "domainNameChop dn n = (domainNameDeptChopOne^^n) dn"
      apply(induction dn n rule: domainNameChop.induct)
        apply (simp_all)
      apply(rename_tac nat,induct_tac nat, simp_all)
      apply(rename_tac n)
      by (metis funpow_swap1)
    
    lemma domainNameChopRotateSuc: "domainNameChop dn (Suc n) = domainNameDeptChopOne (domainNameChop dn n)"
    by(simp add: domainNameChopFunApply)
    
    lemma domainNameChopRotate: "domainNameChop (domainNameDeptChopOne dn) n = domainNameDeptChopOne (domainNameChop dn n)"
      apply(subgoal_tac "domainNameChop (domainNameDeptChopOne dn) n = domainNameChop dn (Suc n)")
       apply simp
       apply(simp add: domainNameChopFunApply)
      apply(case_tac dn)
       by(simp_all)
    
    
    theorem chop_not_decrease_hierarchy: "dn \<le> domainNameChop dn n"
      apply(induction n)
       apply(simp)
       apply(case_tac dn)
       apply(rename_tac name dpt)
       apply (simp)
       apply(simp add:domainNameChopRotate)
       apply (metis chopOne_not_decrease less_eq_refl)
      apply simp
     done
    
    corollary "dn \<le> domainNameDeptChopOne ((domainNameDeptChopOne ^^ n) (dn))"
    by (metis chop_not_decrease_hierarchy domainNameChopFunApply domainNameChopRotateSuc)
      

   text\<open>compute maximum common level of both inputs\<close>
   fun chop_sup :: "domainNameDept \<Rightarrow> domainNameDept \<Rightarrow> domainNameDept" where
      "chop_sup Leaf _ = Leaf" | 
      "chop_sup _ Leaf = Leaf" | 
      "chop_sup (a--as) (b--bs) = (if a \<noteq> b then Leaf else a--(chop_sup as bs))" 

   lemma "chop_sup (''a''--''b''--''c''--Leaf) (''a''--''b''--''d''--Leaf) = ''a'' -- ''b'' -- Leaf" by eval
   lemma "chop_sup (''a''--''b''--''c''--Leaf) (''a''--''x''--''d''--Leaf) = ''a'' -- Leaf" by eval
   lemma "chop_sup (''a''--''b''--''c''--Leaf) (''x''--''x''--''d''--Leaf) = Leaf" by eval

   lemma chop_sup_commute: "chop_sup a b = chop_sup b a"
    apply(induction a b rule: chop_sup.induct)
      apply(rename_tac a)
      apply(simp_all)
    apply(case_tac a, simp_all)
    done
  lemma chop_sup_max1: "a \<le> chop_sup a b"
    apply(induction a b rule: chop_sup.induct)
      by(simp_all)
  lemma chop_sup_max2: "b \<le> chop_sup a b"
    apply(subst chop_sup_commute)
    by(simp add: chop_sup_max1)

   (* don't need this, preserver \<le> on domainNameDept and \<sqsubseteq> on domainName
   instantiation domainNameDept :: partial_order
   begin
     fun leq_domainNameDept :: "domainNameDept \<Rightarrow> domainNameDept \<Rightarrow> bool" (* \<sqsubseteq> *) where 
      "leq_domainNameDept a b = (a \<le> b)"
   instance
      by(intro_classes,simp_all)
   end
   *)
   lemma chop_sup_is_sup: "\<forall>z. a \<le> z \<and> b \<le> z \<longrightarrow> chop_sup a b \<le> z"
    apply(clarify)
    apply(induction a b rule: chop_sup.induct)
      apply(simp_all)
    apply(rule conjI)
     apply(clarify)
     apply(subgoal_tac "z=Leaf")
      apply(simp)
     apply(simp add: uncomparable_sup_is_Top)
    apply(clarify)
    apply(case_tac z)
     by(simp_all)
    


  datatype domainName = DN domainNameDept | Unassigned


  subsubsection \<open>Makeing it a complete Lattice\<close>
    instantiation domainName :: partial_order
    begin
      (* adding trust here would violate transitivity or antsymmetry *)
      fun leq_domainName :: "domainName \<Rightarrow> domainName \<Rightarrow> bool" (* \<sqsubseteq> *) where 
        "leq_domainName Unassigned _ = True" |
        "leq_domainName _ Unassigned = False" |
        "leq_domainName (DN dnA) (DN dnB) = (dnA \<le> dnB)"
    instance
      apply(intro_classes)
      (* x \<sqsubseteq> x *)
        apply(case_tac x)
       apply(simp_all)
      (* x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> z \<Longrightarrow> x \<sqsubseteq> z *)
       apply(case_tac x, rename_tac dnX)
        apply(case_tac y, rename_tac dnY)
         apply(case_tac z, rename_tac dnZ)
          apply(simp_all)
      (* x \<sqsubseteq> y \<Longrightarrow> y \<sqsubseteq> x \<Longrightarrow> x = y *)
      apply(case_tac x, rename_tac dnX)
       apply(case_tac y, rename_tac dnY)
        apply(simp_all)
      apply(metis domainName.exhaust leq_domainName.simps(2))
      done
    end

    lemma "is_Inf {Unassigned, DN Leaf} Unassigned"
      by(simp add: is_Inf_def)
    
    text \<open>The infinum of two elements:\<close>
    fun DN_inf :: "domainName \<Rightarrow> domainName \<Rightarrow> domainName" where
      "DN_inf Unassigned _ = Unassigned" |
      "DN_inf _ Unassigned = Unassigned" |
      "DN_inf (DN a) (DN b) = (if a \<le> b then DN a else if b \<le> a then DN b else Unassigned)"

    lemma "DN_inf (DN (''TUM''--''i8''--Leaf)) (DN (''TUM''--''i20''--Leaf)) = Unassigned" by eval
    lemma "DN_inf (DN (''TUM''--''i8''--Leaf)) (DN (''TUM''--Leaf)) = DN (''TUM'' -- ''i8'' -- Leaf)" by eval
      

    lemma DN_inf_commute: "DN_inf x y = DN_inf y x"
      apply(induction x y rule: DN_inf.induct)
        apply(rename_tac x)
        apply(case_tac x)
         by (simp_all)

    lemma DN_inf_is_inf: "is_inf x y (DN_inf x y)"
      apply(induction x y rule: DN_inf.induct)
        apply(simp add: is_inf_def)
       apply(simp add: is_inf_def)
      apply(simp add: is_inf_def)
      apply(clarify)
      apply(rename_tac z)
      apply(case_tac z)
       apply(simp)
       apply(rename_tac zn)
       apply(simp_all)
      using common_inf_imp_comparable by blast

    
    fun DN_sup :: "domainName \<Rightarrow> domainName \<Rightarrow> domainName" where
      "DN_sup Unassigned a = a" | 
      "DN_sup a Unassigned = a" |
      "DN_sup (DN a) (DN b) = DN (chop_sup a b)"

    lemma DN_sup_commute: "DN_sup x y = DN_sup y x"
      apply(induction x y rule: DN_sup.induct)
        apply(rename_tac x)
        apply(case_tac x)
         by(simp_all add: chop_sup_commute)

    lemma DN_sup_is_sup: "is_sup x y (DN_sup x y)"
      apply(induction x y rule: DN_inf.induct)
        apply(simp add: is_sup_def leq_refl)
       apply(simp add: is_sup_def)
      apply(simp add: is_sup_def chop_sup_max1 chop_sup_max2)
      apply(clarify)
      apply(rename_tac z)
      apply(case_tac z)
       apply(simp)
       apply(rename_tac zn)
       apply(simp_all)
      apply(clarify)
      apply(simp add: chop_sup_is_sup)
      done
   
    text \<open>domainName is a Lattice:\<close>
    instantiation domainName :: lattice
      begin
      instance
        apply intro_classes
         apply(rule_tac x="DN_inf x y" in exI)
         apply(fact DN_inf_is_inf)
        apply(rule_tac x="DN_sup x y" in exI)
        apply(rule DN_sup_is_sup)
       done
    end
    



(*TRUST*)


  datatype domainNameTrust = DN "(domainNameDept \<times> nat)" | Unassigned

    (*transitivity only if trustA \<ge> trust C*)
    fun leq_domainNameTrust :: "domainNameTrust \<Rightarrow> domainNameTrust \<Rightarrow> bool" (infixr "\<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t" 65)  where 
      "leq_domainNameTrust Unassigned _ = True" |
      "leq_domainNameTrust _ Unassigned = False" |
      "leq_domainNameTrust (DN (dnA, trustA)) (DN (dnB, trustB)) = (dnA \<le> (domainNameChop dnB trustB))"

    lemma leq_domainNameTrust_refl: "x \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t x"
      apply(case_tac x)
       apply(rename_tac prod)
       apply(case_tac prod)
       apply(simp add: chop_not_decrease_hierarchy)
      by(simp)
   
   lemma leq_domainNameTrust_NOT_trans: "\<exists>x y z. x \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t y \<and> y \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t z \<and> \<not> x \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t z"
    apply(rule_tac x="DN (''TUM''--Leaf, 0)" in exI)
    apply(rule_tac x="DN (''TUM''--''i8''--Leaf, 1)" in exI)
    apply(rule_tac x="DN (''TUM''--''i8''--Leaf, 0)" in exI)
    apply(simp)
    done

   lemma leq_domainNameTrust_NOT_antisym: "\<exists>x y. x \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t y \<and> y \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t x \<and> x \<noteq> y"
    apply(rule_tac x="DN (Leaf, 3)" in exI)
    apply(rule_tac x="DN (Leaf, 4)" in exI)
    apply(simp)
    done

subsubsection\<open>The network security invariant\<close>

definition default_node_properties :: "domainNameTrust"
  where  "default_node_properties = Unassigned"

text\<open>The sender is, noticing its trust level, on the same or higher hierarchy level as the receiver.\<close>
fun sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> bool" where
  "sinvar G nP = (\<forall> (s, r) \<in> edges G. (nP r) \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP s))"



(*TODO: old legacy function!*)
text\<open>a domain name must be in the supplied tree\<close>
fun verify_globals :: "'v graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> domainTree \<Rightarrow> bool" where
  "verify_globals G nP tree = (\<forall> v \<in> nodes G. 
    case (nP v) of Unassigned \<Rightarrow> True | DN (level, trust) \<Rightarrow> valid_hierarchy_pos tree level
   )"


lemma "verify_globals \<lparr> nodes=set [1,2,3], edges=set [] \<rparr> (\<lambda>n. default_node_properties) (Department ''TUM'' [])"
  by (simp add: default_node_properties_def)


definition receiver_violation :: "bool" where "receiver_violation = False"




thm SecurityInvariant_withOffendingFlows.sinvar_mono_def
lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
  apply(rule_tac SecurityInvariant_withOffendingFlows.sinvar_mono_I_proofrule)
   apply(auto)
  apply(rename_tac nP e1 e2 N E' e1' e2' E)
  apply(blast)
 done


interpretation SecurityInvariant_preliminaries
where sinvar = sinvar
  apply unfold_locales
    apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
    apply(erule_tac exE)
    apply(rename_tac list_edges)
    apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
        apply(auto)[4]
   apply(auto simp add: SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)[1]
  apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_sinvar_mono[OF sinvar_mono])
 apply(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
done


subsubsection \<open>ENF\<close>
  lemma DomainHierarchyNG_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form sinvar (\<lambda> s r. r \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t s)"
    unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def
    by simp
  lemma DomainHierarchyNG_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl sinvar (\<lambda> s r. r \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t s)"
    unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
    apply(rule conjI)
     apply(simp add: DomainHierarchyNG_ENF)
    apply(simp add: leq_domainNameTrust_refl)
  done
  lemma unassigned_default_candidate: "\<forall>nP s r. \<not> (nP r)  \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP s) \<longrightarrow> \<not> (nP r)  \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t default_node_properties"
    apply(clarify)
    apply (simp add: default_node_properties_def) 
    by (metis leq_domainNameTrust.elims(3) leq_domainNameTrust.simps(2))

  definition DomainHierarchyNG_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> domainNameTrust) \<Rightarrow> ('v \<times> 'v) set set" where
  "DomainHierarchyNG_offending_set G nP = (if sinvar G nP then
      {}
     else 
      { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> (nP e2) \<sqsubseteq>\<^sub>t\<^sub>r\<^sub>u\<^sub>s\<^sub>t (nP e1)} })"
  lemma DomainHierarchyNG_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = DomainHierarchyNG_offending_set"
    apply(simp only: fun_eq_iff SecurityInvariant_withOffendingFlows.ENF_offending_set[OF DomainHierarchyNG_ENF] DomainHierarchyNG_offending_set_def)
    apply(rule allI)+
    apply(rename_tac G nP)
    apply(auto split:prod.split_asm prod.split simp add: Let_def)
  done


  lemma Unassigned_unique_default: "otherbot \<noteq> default_node_properties \<Longrightarrow>
         \<exists>G nP gP i f.
            wf_graph G \<and> 
            \<not> sinvar G nP \<and>
            f \<in> SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G nP \<and>
            sinvar (delete_edges G f) nP \<and>
            (i \<in> fst ` f \<and> sinvar G (nP(i := otherbot)))"
    apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_def)
    apply (simp add:graph_ops)
    apply (simp split: prod.split_asm prod.split domainNameTrust.split)
    apply(rule_tac x="\<lparr> nodes={vertex_1,vertex_2}, edges = {(vertex_1,vertex_2)} \<rparr>" in exI, simp)
    apply(rule conjI)
     apply(simp add: wf_graph_def)
    apply(case_tac otherbot)
     apply(rename_tac prod)
     apply(case_tac prod)
     apply(rename_tac dn trustlevel)
     apply(clarify)

     apply(case_tac dn)
  
    (* case (name -- dpt, trustlevel)  *)
      apply(rename_tac name dpt)
      apply(simp)
      apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := Unassigned, vertex_2 := DN (name--dpt, 0 ))" in exI, simp)
      apply(rule_tac x="vertex_1" in exI, simp)
      apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
      apply(simp add:chop_not_decrease_hierarchy)
  
    (* case (Leaf, trustlevel)*)
     apply(simp)
     apply(rule_tac x="(\<lambda> x. default_node_properties)(vertex_1 := Unassigned, vertex_2 := DN (Leaf, 0))" in exI, simp)
     apply(rule_tac x="vertex_1" in exI, simp)
     apply(rule_tac x="{(vertex_1,vertex_2)}" in exI, simp)
  
    (* case Unassigned *)
    apply(simp add: default_node_properties_def)
   done

interpretation DomainHierarchyNG: SecurityInvariant_ACS
where default_node_properties = default_node_properties
and sinvar = sinvar
rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = DomainHierarchyNG_offending_set"
  apply unfold_locales
    apply(rule ballI)
    apply(drule SecurityInvariant_withOffendingFlows.ENF_fsts_refl_instance[OF DomainHierarchyNG_ENF_refl unassigned_default_candidate], simp_all)[1]
   apply(erule default_uniqueness_by_counterexample_ACS)
   apply(drule Unassigned_unique_default) 
   apply(simp)
  apply(fact DomainHierarchyNG_offending_set)
 done




lemma TopoS_DomainHierarchyNG: "SecurityInvariant sinvar default_node_properties receiver_violation"
  unfolding receiver_violation_def by(unfold_locales)




hide_const (open) sinvar receiver_violation

end
