section \<open>Basic Simpset for VCG\<close>
theory IMP2_Basic_Simpset
imports "../basic/Semantics" "../lib/Named_Simpsets" "../lib/IMP2_Utils"
begin
  text \<open>We set up a simpset, \<open>vcg_bb\<close>, which is invoked to unfold some commands in the VCG, 
    and to compute program analysis information.
   \<close>
  
  named_simpset vcg_bb = HOL_basic_ss
  
  ML \<open>
    (* Handy shortcuts *)
    fun vcg_bb_simplify thms ctxt = simplify (Named_Simpsets.put @{named_simpset vcg_bb} ctxt addsimps thms)
    fun vcg_bb_simp_tac thms ctxt = simp_tac (Named_Simpsets.put @{named_simpset vcg_bb} ctxt addsimps thms)
  \<close>
  
  text \<open>Put in ASSUMPTION and NO_MATCH\<close>  
  lemmas [named_ss vcg_bb cong] = ASSUMPTION_cong NO_MATCH_cong
  
  declaration \<open>K
    let
      val asm_sol = mk_solver "ASSUMPTION" (fn ctxt =>
        resolve_tac ctxt [@{thm ASSUMPTION_I}] THEN'
        resolve_tac ctxt (Simplifier.prems_of ctxt))
    in
      Named_Simpsets.map_ctxt @{named_simpset vcg_bb} (
           (fn ctxt => Simplifier.addSolver (ctxt,asm_sol))
        #> (fn ctxt => ctxt addsimprocs [@{simproc NO_MATCH}])
      )
    end
  \<close>

  text \<open>Congruence rules for short-circuit behaviour on if. 
    This is useful, as this simpset has to perform basic computations, 
    like variable name comparison, etc.
    
    Attention: Do not add short-circuit behaviour on \<open>\<and>,\<or>\<close>, or anything that might
      clash with the evaluation of the semantics of aexp or bexp!
    
  \<close>
  (*
    TODO: Conceptually, we have two different things here. The \<and>,\<or> which we use to compute,
      and the \<and>,\<or> that are part of the aval/bval semantics. 
      At the end, we should keep those separated!
  *)
  
    
  lemmas [named_ss vcg_bb cong] = if_weak_cong (*conj_left_cong disj_left_cong*)

  lemma short_circuit: 
    "a\<and>b \<longleftrightarrow> (if a then b else False)"
    "a\<or>b \<longleftrightarrow> (if a then True else b)"
    by auto
    
  
  
  
  text \<open>Protection of user-specified terms, like pre/postcondition and invariants
    from bb-computation\<close>
  
  
  text \<open>Tag to protect user annotations\<close>
  definition "BB_PROTECT \<equiv> \<lambda>a. a"  
  
  lemma BB_PROTECT_cong[named_ss vcg_bb cong]: "BB_PROTECT a = BB_PROTECT a" by simp 
  lemma BB_PROTECT: "p \<equiv> BB_PROTECT p" by (simp add: BB_PROTECT_def)
  
  ML \<open>
    fun mk_BB_PROTECT t = let val T=fastype_of t in 
      Const (@{const_name BB_PROTECT}, T --> T)$t end 
      
    fun dest_BB_PROTECT (Const (@{const_name BB_PROTECT}, _)$t) = t
      | dest_BB_PROTECT t = raise TERM("dest_BB_PROTECT", [t]);
  \<close>
  
  
  text \<open>Basic Logic\<close>  
  lemmas [named_ss vcg_bb] =
    refl if_True if_False HOL.simp_thms
    True_implies_equals False_implies_equals

  text \<open>String Comparison\<close>  
  lemmas [named_ss vcg_bb] =
    char.inject[unfolded short_circuit]
    
  lemma [unfolded short_circuit,named_ss vcg_bb]:
    fixes x y :: char and xs ys :: string
    shows
    "x#xs = y#ys \<longleftrightarrow> x=y \<and> xs=ys" 
    "x#xs \<noteq> []" "[] \<noteq> x#xs"
    by auto

  text \<open>State Query\<close>
  lemma [named_ss vcg_bb]: 
    fixes s::state
    shows
    "(s(x:=v)) x = v"  
    "(s(x:=v)) y = (if x=y then v else s y)"
    by auto

  (* For array indexing, we only decide syntactically equal queries, and leave the rest untouched *)  
  lemma [named_ss vcg_bb]: 
    fixes a::val
    shows
    "(a(i:=pv)) i = pv"  
    by auto
    
    
  text \<open> Local/Global Variables \<close>
    
  text \<open>For the next two lemmas, we use a crude heuristics to ensure that they are not 
    applied to symbolic variable names: A variable name must be a (non-empty) list.\<close>    
  lemma combine_query': "<s|t> (x#xs) = (if is_global (x#xs) then t (x#xs) else s (x#xs))"  
    by (auto simp: combine_query)
  
  lemma combine_upd':
    "<s|t>((x#xs):=v) = (if is_global (x#xs) then <s|t((x#xs):=v)> else <s((x#xs):=v)|t>)"
    by (auto simp: combine_upd)
  
  lemmas [named_ss vcg_bb] = combine_collapse combine_nest
  lemmas [named_ss vcg_bb] = combine_query' combine_upd'
    
    
  lemma query_prog[named_ss vcg_bb]: "(\<pi>(k\<mapsto>v)) k' = (if k'=k then Some v else \<pi> k')" for \<pi> :: program by auto
    
  text \<open>Sets and Computation of Variable Sets\<close>  
  lemmas vcg_bb_set[unfolded short_circuit, named_ss vcg_bb] =
    Un_insert_left Un_insert_right insert_commute insert_absorb2 Un_empty_left Un_empty_right
    insert_iff empty_iff

  lemma set_filter_simps[named_ss vcg_bb]:
    "Set.filter P {} = {}"
    "Set.filter P (insert x xs) = (if P x then insert x (Set.filter P xs) else Set.filter P xs)"
    by auto
  
  lemma set_collect_simps[named_ss vcg_bb]:
    "Set.filter P UNIV = Collect P"
    "Set.filter P (Collect Q) = Collect (\<lambda>x. P x \<and> Q x)"
    "x\<in>UNIV"
    "x\<in>Collect P \<longleftrightarrow> P x"
    "insert x UNIV = UNIV" 
    by auto
    

    
        
  method i_vcg_bb = (simp named_ss vcg_bb: )
  
    
    
end
