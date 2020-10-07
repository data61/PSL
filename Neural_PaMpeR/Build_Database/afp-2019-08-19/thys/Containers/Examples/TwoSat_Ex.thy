(* Title:      Containers/Examples/TwoSat_Ex.thy
   Author:     Andreas Lochbihler, ETH Zurich
   Author:     Peter Lammich, TU Munich *)

section \<open>Formalisation of 2SAT independent of an implementation\<close>

theory TwoSat_Ex imports
  Main
  "HOL-Library.Uprod"
  "Deriving.Compare_Instances" 
begin

type_synonym var = nat
datatype lit = Lit (pos: bool) (var: var)
abbreviation Pos :: "var \<Rightarrow> lit" where "Pos \<equiv> Lit True"
abbreviation Neg :: "var \<Rightarrow> lit" where "Neg \<equiv> Lit False"
type_synonym clause = "lit uprod"
type_synonym cnf = "clause set"

primrec negate :: "lit \<Rightarrow> lit"
where "negate (Lit b v) = Lit (\<not> b) v"

lemma negate_inject [simp]: "negate x = negate y \<longleftrightarrow> x = y"
by(cases x; cases y) simp

lemma double_negate[simp]: "negate (negate l) = l"
  by (cases l) auto

lemma var_negate[simp]: "var (negate l) = var l"  
  by (cases l) auto


type_synonym valuation = "var \<Rightarrow> bool"

definition sat_lit :: "valuation \<Rightarrow> lit \<Rightarrow> bool"
  where "sat_lit \<sigma> l \<longleftrightarrow> (\<sigma> (var l) \<longleftrightarrow> pos l)"

lemma sat_lit_alt: "sat_lit \<sigma> (Lit p v) \<longleftrightarrow> \<sigma> v = p" 
  by (auto simp: sat_lit_def)
  
function sat_clause where
  "sat_clause \<sigma> (Upair l1 l2) \<longleftrightarrow> sat_lit \<sigma> l1 \<or> sat_lit \<sigma> l2"  
  apply (metis surj_pair uprod_exhaust)
  by auto
termination by lexicographic_order
      
definition sat_cnf :: "valuation \<Rightarrow> cnf \<Rightarrow> bool"  
  where "sat_cnf \<sigma> cnf \<longleftrightarrow> (\<forall>cl\<in>cnf. sat_clause \<sigma> cl)"

definition satisfiable :: "cnf \<Rightarrow> bool"
where "satisfiable cnf \<longleftrightarrow> (\<exists>\<sigma>. sat_cnf \<sigma> cnf)"

definition is_2sat :: "cnf \<Rightarrow> bool"
where "is_2sat cnf \<longleftrightarrow> (\<forall>cl\<in>cnf. proper_uprod cl)"

lemma is_2sat_simps [simp]: "is_2sat {}" "is_2sat (insert cl cnf) \<longleftrightarrow> proper_uprod cl \<and> is_2sat cnf"
by(simp_all add: is_2sat_def)
  
lemma negate_sat[simp]: "sat_lit \<sigma> (negate l) \<longleftrightarrow> \<not> sat_lit \<sigma> l"
  by (cases l) (auto simp: sat_lit_def)
    
function edges_of_clause where 
  "edges_of_clause (Upair l1 l2) = {(negate l1, l2), (negate l2, l1)}"
  by (rule uprod_exhaust) auto
termination by lexicographic_order

definition imp_graph :: "cnf \<Rightarrow> (lit \<times> lit) set" where
  "imp_graph cnf = \<Union>(edges_of_clause ` cnf)"
  
lemma imp_graph_alt: "imp_graph cnf = {(negate l1,l2) | l1 l2. Upair l1 l2 \<in> cnf}"  
  unfolding imp_graph_def apply safe
  subgoal for l1 l2 cl by (cases cl; clarsimp; metis Upair_inject)
  using edges_of_clause.simps by blast
  
lemma imp_graph_empty [simp]: "imp_graph {} = {}"
  by (simp add: imp_graph_def)

lemma imp_graph_insert [simp]:
  "imp_graph (insert cl cls) = edges_of_clause cl \<union> imp_graph cls"
  by (auto simp: imp_graph_def)
    
lemma imp_graph_skew_sym: 
  "(l\<^sub>1,l\<^sub>2) \<in> imp_graph cnf \<Longrightarrow> (negate l\<^sub>2, negate l\<^sub>1) \<in> imp_graph cnf"
  unfolding imp_graph_def apply clarsimp 
  subgoal for cl by (cases cl) (auto 4 3 intro: rev_bexI)
  done

lemma imp_graph_rtrancl_skew_sym:    
  "(l\<^sub>1, l\<^sub>2) \<in> (imp_graph cnf)\<^sup>* \<Longrightarrow> (negate l\<^sub>2, negate l\<^sub>1) \<in> (imp_graph cnf)\<^sup>*"
  by (induction rule: rtrancl.induct)(auto dest: imp_graph_skew_sym)  
      
context
  fixes \<sigma> cnf
  assumes sat: "sat_cnf \<sigma> cnf"  
begin  
  lemma imp_step:
    assumes S: "sat_lit \<sigma> l\<^sub>1"  
    assumes I: "(l\<^sub>1, l\<^sub>2) \<in> imp_graph cnf" 
    shows "sat_lit \<sigma> l\<^sub>2"
  proof -
    from I sat have "\<not> sat_lit \<sigma> l\<^sub>1 \<or> sat_lit \<sigma> l\<^sub>2"
      unfolding sat_cnf_def imp_graph_def
      apply clarsimp
      subgoal for x by(cases x)(auto split: if_split_asm)
      done
    with S show ?thesis by simp
  qed 
  
  lemma imp_steps:
    assumes S: "sat_lit \<sigma> l\<^sub>1"  
    assumes I: "(l\<^sub>1, l\<^sub>2) \<in> (imp_graph cnf)\<^sup>*" 
    shows "sat_lit \<sigma> l\<^sub>2"
    using assms(2,1)
    by (induction) (auto intro: imp_step)  

  lemma ln_loop:
    assumes "(l, negate l) \<in> (imp_graph cnf)\<^sup>*"
    shows "\<not> sat_lit \<sigma> l"  
    using imp_steps[OF _ assms] 
    by (cases "sat_lit \<sigma> l") auto  
  
end

lemma loop_imp_unsat:
  assumes "(Pos x, Neg x) \<in> (imp_graph cnf)\<^sup>*"
  assumes "(Neg x, Pos x) \<in> (imp_graph cnf)\<^sup>*"
  shows "\<not> satisfiable cnf"
  using assms ln_loop[of _ cnf "Pos x"] ln_loop[of _ cnf "Neg x"]
  unfolding satisfiable_def by(auto simp add: sat_lit_def)
    
    
(*
  Informal argument why we can find satisfying valuation if
  there are no cycles Pos x \<rightarrow>\<^sup>* Neg x \<rightarrow>\<^sup>* Pos x.

  Assign all variables as follows:
    Let current assignment be A. By assumption, closed and consistent.
    Choose unassigned variable x
    Try to assign Pos x, form transitive closure.
    If this yields a conflict, assign Neg x

    Assume both Pos x and Neg x would yield conflict:
      As current assignment is always closed, we have 
        G\<^sup>*``Pos x \<inter> negate``A = {} and G\<^sup>*``Neg x \<inter> negate``A = {}
        (Otherwise:
          Pos x \<rightarrow>\<^sup>* negate l, l\<in>A
          \<Longrightarrow> l \<rightarrow>\<^sup>* Neg x (skew sym)
          \<Longrightarrow> Neg x \<in> A (A closed, l\<in>A)
          \<Longrightarrow> x not unassigned, contr!
        )
      Thus, conflict must be of form:
        Pos x \<rightarrow>\<^sup>* Pos y, Pos x \<rightarrow>\<^sup>* Neg y
        Neg x \<rightarrow>\<^sup>* Pos z, Neg x \<rightarrow>\<^sup>* Neg z
        
        \<Longrightarrow> (skew sym)
          Pos y \<rightarrow>\<^sup>* Neg x \<Longrightarrow> Pos x \<rightarrow>\<^sup>* Neg x
          Pos z \<rightarrow>\<^sup>* Pos x \<Longrightarrow> Neg x \<rightarrow>\<^sup>* Pos x
          contr to no-cycle assm
*)    
    
definition consistent :: "lit set \<Rightarrow> bool" where
  "consistent ls \<longleftrightarrow> (\<nexists>x. Pos x \<in> ls \<and> Neg x \<in> ls)"

lemma [simp]: "consistent {}" by (auto simp: consistent_def)  
  
definition vars_of_cnf :: "cnf \<Rightarrow> var set" 
where "vars_of_cnf cnf \<equiv> \<Union>cl\<in>cnf. var ` set_uprod cl"
  
lemma eq_SomeD:
  assumes "x = Eps P"
  assumes "\<exists>x. P x"
  shows "P x"
  using assms by (auto simp: someI)  
  
locale construct_sa =
  fixes cnf :: cnf
  assumes FIN: "finite (vars_of_cnf cnf)"  
  assumes NO_CYC: 
    "\<nexists>x. (Pos x, Neg x) \<in> (imp_graph cnf)\<^sup>* \<and> (Neg x, Pos x) \<in> (imp_graph cnf)\<^sup>*"
  assumes TSAT: "is_2sat cnf"
begin  
  abbreviation "G \<equiv> imp_graph cnf"

  function extend :: "lit set \<Rightarrow> lit set" where
    "extend ls = (
      if vars_of_cnf cnf \<subseteq> var ` ls then ls 
      else let
        x = SOME x. x \<in> vars_of_cnf cnf - var ` ls
      in
        if consistent (ls \<union> G\<^sup>* `` {Pos x}) then
          extend (ls \<union> G\<^sup>* `` {Pos x})
        else
          extend (ls \<union> G\<^sup>* `` {Neg x})
    )"
    by pat_completeness auto
  termination 
    apply (relation "inv_image finite_psubset (\<lambda>ls. vars_of_cnf cnf - var`ls)")
    apply simp
    apply (drule eq_SomeD; auto simp: FIN)  
    apply (drule eq_SomeD; auto simp: FIN)  
    done

  declare extend.simps[simp del]    
      
  lemma extend_vars: "vars_of_cnf cnf \<subseteq> var ` extend ls" 
    apply (induction ls rule: extend.induct) 
    apply (subst extend.simps)  
    apply (auto split: if_splits simp: Let_def)
    done
      
  lemma extend_cons_closed_aux:
    assumes "consistent ls"
    assumes "G `` ls \<subseteq> ls"
    shows "consistent (extend ls) \<and> G `` extend ls \<subseteq> extend ls"  
    using assms(1,2)
  proof (induction ls rule: extend.induct)
    case (1 ls)
      
    show ?case 
    proof (cases "vars_of_cnf cnf \<subseteq> var`ls")
      case True thus ?thesis using "1.prems"
        by(subst (1 2 3) extend.simps) auto
    next
      case [simp]: False
      define x where "x = (SOME x. x \<in> vars_of_cnf cnf - var ` ls)"  
      with False have XI: "x \<in> vars_of_cnf cnf - var ` ls" 
        by (metis (full_types) DiffI someI_ex subsetI)

      show ?thesis proof (cases "consistent (ls \<union> G\<^sup>*``{Pos x})")
        case CPOS [simp]: True
        from "1.prems" have CL: "G `` (ls \<union> G\<^sup>* `` {Pos x}) \<subseteq> ls \<union> G\<^sup>* `` {Pos x}"
          by auto
            
        show ?thesis 
          using "1.IH"(1)[OF False x_def CPOS CPOS CL]
          unfolding extend.simps[of ls]
          unfolding x_def[symmetric]
          by auto
      next
        case NCPOS: False
          
        from "1.prems" have CL: "G `` (ls \<union> G\<^sup>* `` {Neg x}) \<subseteq> ls \<union> G\<^sup>* `` {Neg x}"
          by auto
          
        show ?thesis
        proof (cases "consistent (ls \<union> G\<^sup>* `` {Neg x})")  
          case CNEG[simp]: True
          show ?thesis 
            using "1.IH"(2)[OF False x_def NCPOS CNEG CL] NCPOS
            unfolding extend.simps[of ls] x_def[symmetric]
            by auto
        next
          case NCNEG: False
            
          have X1: "(l, negate l)\<in> G\<^sup>*"
            if UNASS: "var l \<notin> var ` ls" and "\<not> consistent (ls \<union> G\<^sup>* `` {l})" for l
          proof -
            from that(2) obtain y where X1: "Pos y \<in> ls \<union> G\<^sup>*``{l}" "Neg y \<in> ls \<union> G\<^sup>*``{l}"
              unfolding consistent_def by auto
            with "1.prems" have "(l, Pos y) \<in> G\<^sup>* \<or> (l, Neg y) \<in> G\<^sup>*"   
              unfolding consistent_def by auto
            hence X2: "(l, Pos y) \<in> G\<^sup>* \<and> (l, Neg y) \<in> G\<^sup>*"
            proof (safe; rule_tac ccontr)
              assume "(l, Pos y) \<in> G\<^sup>*" "(l, Neg y)\<notin>G\<^sup>*"
              hence "(Neg y,negate l)\<in>G\<^sup>*" "Neg y \<in> ls" 
                using X1 by (auto dest: imp_graph_rtrancl_skew_sym)
              with CL have "negate l \<in> ls"
                by (metis "1.prems"(2) ImageI Image_closed_trancl)    
              with UNASS show False by (cases l) force+  
            next
              assume "(l, Neg y) \<in> G\<^sup>*" "(l, Pos y) \<notin> G\<^sup>*"
              hence "(Pos y, negate l) \<in> G\<^sup>*" "Pos y \<in> ls" 
                using X1 by (auto dest: imp_graph_rtrancl_skew_sym)
              with CL have "negate l \<in> ls"
                by (metis "1.prems"(2) ImageI Image_closed_trancl)    
              with UNASS show False by (cases l) force+  
            qed
            from X2 imp_graph_rtrancl_skew_sym[of _ _ cnf] have "(Neg y, negate l) \<in> G\<^sup>*"
              by force
            with X2 show ?thesis by auto    
          qed
            
          from X1[of "Pos x", OF _ NCPOS] XI have "(Pos x, Neg x)\<in>G\<^sup>*" by auto  
          moreover from X1[of "Neg x", OF _ NCNEG] XI have "(Neg x, Pos x)\<in>G\<^sup>*" by auto
          ultimately have False using NO_CYC by blast   
          thus ?thesis by blast
        qed
      qed
    qed
  qed 
    
  lemma extend_cons_closed:
    "consistent (extend {})" 
    "G `` extend {} \<subseteq> extend {}"  
    using extend_cons_closed_aux[of "{}"] 
    by auto

      
  lemma CCV_sat:
    assumes CONS: "consistent ls"
    assumes CLOSED: "G``ls \<subseteq> ls"
    assumes VARS: "vars_of_cnf cnf \<subseteq> var`ls"  
    shows "sat_cnf (\<lambda>x. Pos x \<in> ls) cnf"  
    unfolding sat_cnf_def
  proof (rule, rule ccontr)
    fix cl
    assume "cl\<in>cnf"
    with TSAT obtain l1 l2 where [simp]: "cl = Upair l1 l2" "l1 \<noteq> l2"
      unfolding is_2sat_def
      by(fastforce simp add: proper_uprod_def dest!: bspec split: uprod_split_asm)
      
    assume "\<not> sat_clause (\<lambda>x. Pos x \<in> ls) cl"
    hence "l1 \<notin> ls" "l2 \<notin> ls" using \<open>consistent ls\<close> 
      apply (auto simp: sat_lit_def consistent_def)
      apply (cases l1; cases l2; auto)+
      done  
    
    from VARS \<open>cl \<in> cnf\<close> have "var l1 \<in> var ` ls" 
      by (auto 4 3 simp: vars_of_cnf_def)
    with \<open>l1 \<notin> ls\<close> have "negate l1 \<in> ls"
    proof -
      have "\<forall>L n f. \<exists>l. ((n::nat) \<notin> f ` L \<or> (l::lit) \<in> L) \<and> (n \<notin> f ` L \<or> f l = n)"
        by blast
      then show ?thesis
        by (metis (no_types) \<open>l1 \<notin> ls\<close> \<open>var l1 \<in> var ` ls\<close> lit.expand negate_sat var_negate)
    qed

    moreover from \<open>cl \<in> cnf\<close> have "(negate l1, l2) \<in> G" 
      unfolding imp_graph_def by(auto intro: rev_bexI)
    ultimately have "l2 \<in> ls" using CLOSED by auto
    thus False using \<open>l2 \<notin> ls\<close> by auto
  qed

  lemma sat: "satisfiable cnf"
    using CCV_sat[OF extend_cons_closed extend_vars]
    by(auto   simp add: satisfiable_def)
      
end

  
lemma imp_graph_vars:
  assumes "(l, l') \<in> imp_graph cnf"  
  shows "var l \<in> vars_of_cnf cnf" 
  using assms unfolding imp_graph_def vars_of_cnf_def
  apply (clarsimp elim!: rev_bexI)
  subgoal for x by(cases x)(auto split: uprod_split_asm if_split_asm)
  done

theorem finite_2sat_iff:
  assumes FIN: "finite (vars_of_cnf cnf)"
  assumes TSAT: "is_2sat cnf"  
  shows "satisfiable cnf 
    \<longleftrightarrow> (\<forall>x\<in>vars_of_cnf cnf. 
          \<not> ((Pos x, Neg x) \<in> (imp_graph cnf)\<^sup>* \<and> (Neg x, Pos x) \<in> (imp_graph cnf)\<^sup>* ))"
  apply (safe;clarsimp?; (auto dest: loop_imp_unsat;fail)?)
proof -
  assume " \<forall>x\<in>vars_of_cnf cnf.
     (Pos x, Neg x) \<in> (imp_graph cnf)\<^sup>* \<longrightarrow> (Neg x, Pos x) \<notin> (imp_graph cnf)\<^sup>*"
  then interpret construct_sa cnf
    apply (unfold_locales)
    using FIN TSAT apply auto
    by (metis converse_rtranclE imp_graph_vars lit.inject lit.sel(2))
  
  from sat show "satisfiable cnf" .
qed

derive linorder lit


subsection \<open>Finiteness\<close>
definition "lits_of_cnf cnf = Pos`vars_of_cnf cnf \<union> Neg`vars_of_cnf cnf"

lemma inj_on_Pos [simp]: "inj_on Pos A" 
  and inj_on_Neg [simp]: "inj_on Neg A"
by(auto simp add: inj_on_def)

lemma lits_of_cnf_finite[iff]:
  "finite (lits_of_cnf cnf) \<longleftrightarrow> finite (vars_of_cnf cnf)"
proof -
  show ?thesis
    unfolding lits_of_cnf_def 
    by (auto simp: finite_image_iff)
qed  
  
lemma vars_of_cnf_finite[simp, intro]:
  "finite cnf \<Longrightarrow> finite (vars_of_cnf cnf)"
  unfolding vars_of_cnf_def by auto

lemma lit_eq_negate_conv[simp]:
  "Lit p v = negate l \<longleftrightarrow> l = Lit (\<not>p) v"
  "negate l = Lit p v \<longleftrightarrow> l = Lit (\<not>p) v"
  by (cases l; auto)+
  
lemma imp_graph_nodes: "imp_graph cnf \<subseteq> lits_of_cnf cnf \<times> lits_of_cnf cnf"
  unfolding imp_graph_def
  apply clarsimp
  subgoal for l1 l2 cl 
    by (cases cl; cases l1; cases l2)(fastforce simp: lits_of_cnf_def vars_of_cnf_def)
  done
    
lemma imp_graph_finite[simp, intro]: "finite (vars_of_cnf cnf) \<Longrightarrow> finite (imp_graph cnf)"
  using finite_subset[OF imp_graph_nodes] by blast

end
