signature CARD_ELIMINATION =
sig
  val cancel_card_constraint: thm -> thm
  val cancel_card_constraint_attr: attribute
end

structure Card_Elimination : CARD_ELIMINATION =
struct

  (* turns A ==> B[CARD('a)] ==> C[CARD('a), CARD('b)] ==> ... ==> Z 
    into CARD('a) = n1 ==> CARD('b) = n2 ==> A ==> B[n1] ==> C[n1,n2] ==> ... ==> Z *)
  fun extract_card_type ctxt thm = let
    val prop = Thm.prop_of thm 
    fun add_match_terms f t = (if f t then insert (op =) t else I) #>
      (case t of         
        t1 $ t2 => add_match_terms f t1 #> add_match_terms f t2
      | Abs (_,_,t1) => add_match_terms f t1
      | _ => I)
    fun replace_terms xys t = (case AList.lookup (op =) xys t of SOME y => y
      | NONE => case t of
        t1 $ t2 => replace_terms xys t1 $ replace_terms xys t2
      | Abs (a,b,t1) => Abs (a,b,replace_terms xys t1)
      | _ => t)
    fun find_card (Const (c,_) $ Const (t,_)) = (c = @{const_name Finite_Set.card} 
          andalso t = @{const_name Orderings.top_class.top}) 
      | find_card _ = false    
    val card_ts = add_match_terms find_card prop []
    val vars = Term.add_vars prop []
    val all_tvars = Term.add_tvars prop []
    val all_tfrees = map TFree (Variable.variant_frees ctxt [prop] (map (apfst fst) all_tvars))
    val ns = map_index (fn (i,_) => ("n" ^ string_of_int i, @{typ nat})) card_ts
    val substT_map = map fst all_tvars ~~ all_tfrees
    val substT = I subst_TVars substT_map
    val free_ns = Variable.variant_frees ctxt [prop] (map (apfst fst) vars @ ns)
    val all_frees = map (substT o Free) free_ns
    val ns = drop (length vars) all_frees
    val subst = subst_vars (substT_map, map fst vars ~~ (take (length vars) all_frees))
    val prop' = subst prop
    val match_card_ns = add_match_terms find_card prop' [] ~~ rev ns
    val prop'' = replace_terms match_card_ns prop'
    val eqs = map (HOLogic.mk_eq #> HOLogic.mk_Trueprop) match_card_ns |> rev
    val new_thm = Goal.prove ctxt (map fst free_ns) eqs prop'' (fn {prems = prems, context = ctxt} => 
      unfold_tac ctxt (map (fn thm => @{thm sym} OF [thm]) prems)
      THEN resolve_tac ctxt [thm] 1
      THEN (REPEAT (assume_tac ctxt 1))) 
  in 
    (length ns, new_thm)
  end

  (* turns A ==> B ==> C into A /\ B ==> C *)
  (* does not properly work in case of nested meta-implications and meta-quantification *)
  (* TODO: fix and simplify *)
  fun combine_first_prems ctxt thm = let
    val prop = Thm.prop_of thm
    val (p1 :: p2 :: prems) = Thm.prems_of thm
    val concl = Thm.concl_of thm
    val all_tvars = Term.add_tvars prop []
    val all_tfrees = map TFree (Variable.variant_frees ctxt [prop] (map (apfst fst) all_tvars))
    val substT_map = map fst all_tvars ~~ all_tfrees
    val prop' = subst_TVars substT_map prop
    val all_vars = Term.add_vars prop' []
    val free_ns = Variable.variant_frees ctxt [prop'] (map (apfst fst) all_vars)
    val all_frees = map Free free_ns
    val subst = subst_vars (substT_map, map fst all_vars ~~ all_frees)
    
    val p1 = subst p1
    val p2 = subst p2
    val prems = map subst prems
    val concl = subst concl
    val p = HOLogic.mk_conj (HOLogic.dest_Trueprop p1, HOLogic.dest_Trueprop p2)
      |> HOLogic.mk_Trueprop
  in
    Goal.prove ctxt (map fst free_ns) (p :: prems) concl (fn {prems = prems, context = ctxt} =>
      let 
        val p = hd prems
        val p1 = @{thm conjunct1} OF [p]
        val p2 = @{thm conjunct2} OF [p]
        val prems = tl prems
      in           
        resolve_tac ctxt [thm OF (p1 :: p2 :: prems)] 1       
      end)
  end

  (* turns CARD('a) = n1 ==> A ==> B ==> C into
        A ==> B ==> n1 != 0 ==> C *)
  fun eliminate_card_constraint ctxt thm = let
    val v = Thm.ctyp_of ctxt (Thm.prems_of thm |> hd |> (fn t => Term.add_tvars t [] |> hd) |> TVar)
    val thm = Internalize_Sort.internalize_sort v thm |> snd
    val thm = combine_first_prems ctxt thm
    val thm = (thm OF @{thms type_impl_card_n}) |> Local_Typedef.cancel_type_definition
    val thm = thm OF @{thms n_zero_nonempty}
    val thm = rotate_prems 1 thm
  in 
    thm
  end

  (* turns CARD('a) = n1 ==> ... ==> CARD('z) = n_z ==> A ==> B ==> C into
        A ==> B ==> n1 != 0 ==> ... ==> n_z != 0 ==> C *)
  fun eliminate_card_constraints ctxt thm n = 
    fold (K (eliminate_card_constraint ctxt)) (replicate n true) thm
    
  (* turns A ==> B[CARD('a)] ==> C[CARD('a), CARD('b)] ==> ... ==> Z 
    into A ==> B[n1] ==> C[n1,n2] ==> ... ==> n1 != 0 ==> n2 != 0 ==> Z *)
  fun cancel_card_constraint thm = let
    val ctxt = Proof_Context.init_global (Thm.theory_of_thm thm)
    val (n,thm) = extract_card_type ctxt thm
  in 
    eliminate_card_constraints ctxt thm n
  end

  val cancel_card_constraint_attr = Thm.rule_attribute [] (K cancel_card_constraint);

  val _ = Context.>> (Context.map_theory (Attrib.setup @{binding cancel_card_constraint} 
    (Scan.succeed cancel_card_constraint_attr) "cancels carrier constraints")) 
end