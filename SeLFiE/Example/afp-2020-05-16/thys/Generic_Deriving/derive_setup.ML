open Derive_Util

signature DERIVE_SETUP =
sig
  val prove_class_transfer : string -> theory -> Proof.state
  val define_class_law : string -> Proof.context -> (thm * thm * thm option * term list * local_theory)
end

structure Derive_Setup : DERIVE_SETUP =
struct     

fun get_class_info thy classname = Symtab.lookup (Class_Data.get thy) classname

fun 
  replace_superclasses lthy (s $ t) = replace_superclasses lthy s $ replace_superclasses lthy t |
  replace_superclasses lthy (Const (n,T)) = 
    let 
      val is_class = Long_Name.base_name n
      val class = Syntax.parse_sort lthy is_class handle ERROR _ => []
    in
      if null class then Const (n,T) else
      let
        val class_data = get_class_info (Proof_Context.theory_of lthy) (hd class)
      in
        if is_some class_data then the (#class_law_const (the class_data)) else Const (n,T)
      end
    end |
  replace_superclasses _ t = t   

fun 
  contains_axioms cn (s $ t) = contains_axioms cn s orelse contains_axioms cn t |
  contains_axioms cn (Const (n,_)) =
    let
      val is_class = Long_Name.base_name n
    in 
      if is_class = cn ^ "_axioms" 
        then true
        else false
    end |
  contains_axioms _ _ = false

fun define_class_law classname lthy  =
let
  val class_def = Proof_Context.get_thm lthy ("class." ^ classname ^ "_def")
  val has_axioms = 
    contains_axioms classname 
                    (class_def |> Thm.full_prop_of |> Logic.unvarify_global |>  Logic.dest_equals |> snd)
  val (axioms_def,(vars,class_law)) = class_def 
                   |> (if has_axioms 
                        then 
                          let val axioms_def = Proof_Context.get_thm lthy ("class." ^ classname ^ "_axioms_def")
                          in Local_Defs.unfold lthy [axioms_def] #> pair (SOME axioms_def) end
                        else (pair NONE))
                   ||> Thm.full_prop_of ||> Logic.unvarify_global ||> Logic.dest_equals 
                   ||> apfst (strip_comb #> snd) ||> apsnd (replace_superclasses lthy)

  val class_law_name = classname ^ "_class_law"
  val class_law_lhs = list_comb ((Free (class_law_name,(map (dest_Free #> snd) vars) ---> \<^typ>\<open>bool\<close>)),vars)
  val class_law_eq = HOLogic.Trueprop $ HOLogic.mk_eq (class_law_lhs,class_law)
  val ((_,(_,class_law_thm)),lthy') = Specification.definition NONE [] [] ((Binding.empty, []), class_law_eq) lthy
  
  val ctxt_thy = Proof_Context.init_global (Proof_Context.theory_of lthy')
  val class_law_thm_export = singleton (Proof_Context.export lthy' ctxt_thy) class_law_thm
in
  (class_law_thm_export,class_def,axioms_def,vars,lthy')
end

fun transfer_op lthy from to var =  
let
  fun convert_arg (T,i) =
    case T of (TFree (_,_)) => from $ (Bound i) |
              _ => Bound i
  fun 
    abstract [] t = t |
    abstract (x::xs) t = (Abs (x, dummyT, abstract xs t))          
  val (v,T) = dest_Free var
  val (binders,body) = strip_type T
  val argnames = Name.invent_names (Variable.names_of lthy) "x" binders |> map fst
  val args_converted = map convert_arg (binders ~~ (List.tabulate (length binders,fn n => (length binders)-(n+1))))
  val op_call = list_comb ((Free (v,T)),args_converted)
  val op_converted = 
    case body of
      (TFree (_,_)) => to $ op_call |
      _ => op_call
in
  abstract argnames op_converted
end

fun prove_class_transfer classname thy = 
let
  fun add_info info thy = Class_Data.put (Symtab.update ((#classname info),info) (Class_Data.get thy)) thy
  val class = Syntax.parse_sort (Proof_Context.init_global thy) classname
  val classname_full = hd class
  val axioms = Axclass.get_info thy classname_full |> #axioms
  val (class_law,class_def,axioms_def,vars,lthy) = define_class_law classname (Named_Target.theory_init thy) 
  (* Exit so that class law is defined properly before the next step *)
  val thy' = Named_Target.exit lthy
  val lthy' = Named_Target.theory_init thy'

  val tfree_dt = get_tvar (map (dest_Free #> snd) vars)
  val tfree_rep = let val (n,s) = tfree_dt |> dest_TFree in Name.invent_names (Name.make_context [n]) "'a" [s] end |> hd |> TFree
  val from = Free ("from",tfree_rep --> tfree_dt)
  val to   = Free ("to",tfree_dt --> tfree_rep)

  val class_law_const = Thm.full_prop_of class_law |> HOLogic.dest_Trueprop |> HOLogic.dest_eq |> fst |> strip_comb |> fst
  val class_law_const_dummy = dest_Const class_law_const |> apsnd (K dummyT) |> Const
  val class_law_var = (Term.add_tvars class_law_const []) |> hd |> fst
  val class_law_const_dt = subst_vars ([(class_law_var,tfree_dt)],[]) class_law_const 
  val class_law_const_rep = subst_vars ([(class_law_var,tfree_rep)],[]) class_law_const

  val assm_iso = HOLogic.mk_Trueprop (Const (\<^const_name>\<open>Derive.iso\<close>,dummyT) $ from $ to)
  val assm_class = HOLogic.mk_Trueprop (list_comb (class_law_const_dt,vars))
  val vars_transfer = map (transfer_op lthy' from to) vars
  val transfer_concl = HOLogic.mk_Trueprop (list_comb (class_law_const_rep,vars_transfer))
  val transfer_term = Logic.mk_implies (assm_iso, (Logic.mk_implies (assm_class, transfer_concl)))
  val transfer_term_inf = Type_Infer_Context.infer_types lthy' [transfer_term] |> hd

  fun after_qed thms lthy =
    (fold_map (fn lthy => fn thm => (Local_Theory.note ((Binding.name (classname ^ "_transfer"),[]), lthy) thm))
                    thms lthy)    
      |> (fn (thms,lthy) => 
            Local_Theory.background_theory 
              (add_info {classname = classname_full, class = class, params = NONE, class_law = SOME class_law, class_law_const = SOME class_law_const_dummy, ops = SOME vars, transfer_law = SOME thms, axioms = SOME axioms, axioms_def = axioms_def, class_def = SOME class_def, equivalence_thm = NONE})
              lthy)
      |> Local_Theory.exit 
in 
  Proof.theorem NONE after_qed [[(transfer_term_inf, [])]] lthy' 
end

val _ =
  Outer_Syntax.command \<^command_keyword>\<open>derive_generic_setup\<close> "prepare a class for derivation"
    (Parse.name >> (fn c =>
      Toplevel.theory_to_proof (fn thy => if has_class_law c thy 
                                          then prove_class_transfer c thy
                                          else error ("Class " ^ c ^ " has no associated laws, no need to call derive_setup"))))

end