section \<open>\isaheader{Verified BFS Implementation in ML}\<close>
theory Bfs_Impl
imports 
  Refine_Monadic.Breadth_First_Search
  Collections.Refine_Dflt_Only_ICF
begin
  text \<open>
    Originally, this was part of our submission to the 
    VSTTE 2010 Verification Competition. Some slight changes have been applied
    since the submitted version.
\<close>


  text \<open>
    In the \<open>Breadth_First_Search\<close>-theory, we verified an abstract 
    version of the algorithm. This abstract version tried to reflect the
    given pseudocode specification as precisely as possible.

    However, it was not executable, as it was nondeterministic. Hence,
    we now refine our algorithm to an executable specification, and use
    Isabelle/HOLs code generator to generate ML-code.

    The implementation uses the Isabelle Collection Framework (ICF)
    (Available at @{url "http://isa-afp.org/entries/Collections.shtml"}),
    to provide efficient set implementations. We choose a hashset 
    (backed by a Red Black Tree) for the visited set, and lists for
    all other sets. Moreover, we fix the node type to natural numbers.
\<close>

  text \<open>
    The following algorithm is a straightforward rewriting of the 
    original algorithm. We only exchanged the abstract set operations by
    concrete operations on the data structures provided by the ICF.

    The operations of the list-set implementation are named
    \<open>ls_xxx\<close>, the ones of the hashset are named \<open>hs_xxx\<close>.
\<close>

  definition bfs_impl :: "(nat \<Rightarrow> nat ls) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat option nres)"
    where "bfs_impl succ src dst \<equiv> do {
    (f,_,_,_,d) \<leftarrow> WHILE
      (\<lambda>(f,V,C,N,d). f=False \<and> \<not> ls.isEmpty C)
      (\<lambda>(f,V,C,N,d). do {
        v \<leftarrow> RETURN (the (ls.sel C (\<lambda>_. True))); let C = ls.delete v C;
        if v=dst then RETURN (True,hs.empty (),ls.empty (),ls.empty (),d)
        else do {
          (V,N) \<leftarrow> FOREACH (ls.\<alpha> (succ v)) (\<lambda>w (V,N). 
            if (\<not> hs.memb w V) then 
               RETURN (hs.ins w V, ls.ins_dj w N) 
            else RETURN (V,N)
          ) (V,N);
          if (ls.isEmpty C) then do {
            let C=N; 
            let N=ls.empty (); 
            let d=d+1;
            RETURN (f,V,C,N,d)
          } else RETURN (f,V,C,N,d)
        }
      })
      (False,hs.sng src,ls.sng src, ls.empty (),0::nat);
    if f then RETURN (Some d) else RETURN None
    }"

  text \<open>Auxilliary lemma to initialize the refinement prover.\<close>
  (*lemma [refine]: "(ls.\<alpha> \<circ> succ) v = ls.\<alpha> (succ v)"
    by auto*)

  (* TODO/FIXME:
    There is too much redundancy in the xx_correct - lemmas.
    They do not include the automtically instantiated generic algorithms,
    and they are independent of adding new operations to the interface or to
    the rb-interface
    *)

  text \<open>
    It is quite easy to show that the implementation respects the 
    specification, as most work is done by the refinement framework.\<close>
  theorem bfs_impl_correct:
    shows "bfs_impl succ src dst \<le> Graph.bfs_spec (ls.\<alpha>\<circ>succ) src dst"
  proof -
    txt \<open>As list-sets are always finite, our setting satisfies the
      finitely-branching assumption made about graphs\<close>
    interpret Graph "ls.\<alpha>\<circ>succ"
      by unfold_locales simp

    txt \<open>The refinement framework can prove automatically that
      the implementation refines the abstract algorithm.

      The notation \<open>S \<le> \<Down>R S'\<close> means, that the program \<open>S\<close>
      refines the program \<open>S'\<close> w.r.t.\ the refinement relation 
      (also called coupling invariant occasionally) \<open>R\<close>.

      In our case, the refinement relation is the identity, as
      the result type was not refined.
\<close>

    have "bfs_impl succ src dst \<le> \<Down>Id (Graph.bfs (ls.\<alpha>\<circ>succ) src dst)"
      unfolding bfs_impl_def bfs_def

      apply (refine_rcg)
      apply (refine_dref_type)

      apply (simp_all add: refine_hsimp refine_rel_defs
        hs.correct hs.sng_correct ls.correct ls.sng_correct
        split: prod.split prod.split_asm)
      apply (rule inj_on_id)
      apply (simp_all add: refine_hsimp refine_rel_defs
        hs.correct hs.sng_correct ls.correct ls.sng_correct
        split: prod.split prod.split_asm)
      done
    txt \<open>The result then follows due to transitivity of refinement.\<close>
    also have "\<dots> \<le> bfs_spec src dst"
      by (simp add: bfs_correct)
    finally show ?thesis .
  qed

  text \<open>The last step is to actually generate executable ML-code.
\<close>

  text \<open>
    We first use the partial-correctness code generator of our framework
    to automatically turn the algorithm described in our framework into
    a function that is independent from our framework. This step also
    removes the last nondeterminism, that has remained in the iteration order
    of the inner loop.

    The result of the function is an option type, returning \<open>None\<close>
    for nontermination. Inside this option-type, there is the option type
    that encodes whether we return with failure or a distance.
\<close>
  schematic_goal bfs_code_refine_aux: 
    "nres_of ?bfs_code \<le> bfs_impl succ src dst"
    unfolding bfs_impl_def
    apply (refine_transfer)
    done

  concrete_definition bfs_code for succ src dst uses bfs_code_refine_aux

  text \<open>
    As a last step, we make the correctness property independent of our 
    refinement framework. This step drastically decreases the trusted code 
    base, as it completely eliminates the specifications made in the
    refinement framework from the trusted code base.

    The following theorem solves both verification tasks, without depending
    on any concepts of the refinement framework, except the deterministic result
    monad.
\<close>
  theorem bfs_code_correct:
    "bfs_code succ src dst = dRETURN None 
      \<Longrightarrow> \<not>(Graph.conn (ls.\<alpha> \<circ> succ) src dst)" 
    "bfs_code succ src dst = dRETURN (Some d) 
      \<Longrightarrow> Graph.conn (ls.\<alpha> \<circ> succ) src dst 
          \<and> Graph.min_dist (ls.\<alpha> \<circ> succ) src dst = d"
    "bfs_code succ src dst \<noteq> dFAIL"
  proof -
    interpret Graph "ls.\<alpha>\<circ>succ"
      by unfold_locales simp
    
    from order_trans[OF bfs_code.refine bfs_impl_correct, of succ src dst]
    show "bfs_code succ src dst = dRETURN None 
      \<Longrightarrow> \<not>(Graph.conn (ls.\<alpha> \<circ> succ) src dst)" 
      "bfs_code succ src dst = dRETURN (Some d) 
      \<Longrightarrow> Graph.conn (ls.\<alpha> \<circ> succ) src dst 
          \<and> Graph.min_dist (ls.\<alpha> \<circ> succ) src dst = d"
      "bfs_code succ src dst \<noteq> dFAIL"
      apply (unfold bfs_spec_def)
      apply (auto split: option.split_asm)
      done
  qed
      
  text \<open>Now we can use the code-generator of Isabelle/HOL to generate
    code into various target languages:\<close>
  export_code bfs_code checking SML
  export_code bfs_code checking OCaml?
  export_code bfs_code checking Haskell?
  export_code bfs_code checking Scala

  text \<open>The generated code is most conveniently executed within 
    Isabelle/HOL itself. We use a small test graph here:\<close>

  definition nat_list:: "nat list \<Rightarrow> _" where "nat_list \<equiv> dlist_of_list"
  ML_val \<open>
    fun il l = @{code nat_list} (map @{code nat_of_integer} l)
    fun bfs succ s d = 
      @{code bfs_code} (succ o @{code integer_of_nat})
        (@{code nat_of_integer} s) (@{code nat_of_integer} d)

    (* Define a test graph. *)
    fun succ 1 = il [2,3]
        | succ 2 = il [4]
        | succ 4 = il [5]
        | succ 5 = il [2]
        | succ 3 = il [6]
        | succ _ = il [];

    (* Execute algorithm for some node pairs. *)
    bfs succ 1 1;
    bfs succ 1 2;
    bfs succ 1 5;
    bfs succ 1 7;
\<close>

end
