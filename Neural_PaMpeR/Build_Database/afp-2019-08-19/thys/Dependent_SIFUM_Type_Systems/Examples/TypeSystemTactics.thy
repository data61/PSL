theory TypeSystemTactics
imports "../Compositionality"
        "../TypeSystem"
        "HOL-Eisbach.Eisbach_Tools"
begin

(* Some Eisbach magic to get around Eisbach and locales not getting along *)

ML \<open>
structure Data = Proof_Data
(
  type T = morphism
  fun init _ = Morphism.identity;
);
\<close>

method_setup wrap = 
  \<open>Method.text_closure >> (fn text => fn ctxt =>
    let
      val morph = Data.get ctxt;

      fun safe_fact thm =
        perhaps (try (Morphism.thm morph)) thm;
       
      val morph' = Morphism.morphism "safe" 
        {binding = [Morphism.binding morph],
         fact = [map safe_fact],
         term = [Morphism.term morph],
         typ = [Morphism.typ morph]}
      
      val text' = Method.map_source (map (Token.transform morph')) text;
    in Method.evaluate_runtime text' ctxt end)\<close>

method_setup print_headgoal = 
  \<open>Scan.succeed (fn ctxt =>
  SIMPLE_METHOD
    (SUBGOAL (fn (t,_) => 
    (Output.writeln 
    (Pretty.string_of (Syntax.pretty_term ctxt t)); all_tac)) 1))\<close>

named_theorems aexpr and bexpr and prog and custom_if
context sifum_types_assign
begin

(* More Eisbach magic to get around Eisbach and mutual recursion not getting along *)

method_setup call_by_name = \<open>Scan.lift Parse.string >> 
  (fn str => fn ctxt => 
    case (try (Method.check_src ctxt) (Token.make_src (str, Position.none) [])) of
    SOME src => Method.evaluate (Method.Source src) ctxt
    | _ => Method.fail)\<close>

(* Eisbach tactics for partially automating has_type proofs *)

method seq_tac 
  methods tac = 
  (wrap \<open>rule seq_type\<close>, tac, tac) 

method anno_tac 
  methods tac = 
  (wrap \<open>rule anno_type[OF HOL.refl HOL.refl HOL.refl], 
         clarsimp, 
        tac, 
       simp, 
      fastforce simp: add_anno_def subtype_def pred_entailment_def 
                      pred_def bot_Sec_def[symmetric],
     simp add: add_anno_def,
    simp\<close>) 


method assign\<^sub>2_tac =
     wrap \<open>rule assign\<^sub>2\<close>, 
        simp, 
       solves \<open>rule aexpr; simp\<close>, 
      (fastforce),
     simp,
    simp


method assign\<^sub>1_tac =
   wrap \<open>rule assign\<^sub>1,
        simp,
       simp,
      solves \<open>rule aexpr;  simp\<close>,
      simp,
     clarsimp simp: subtype_def pred_def,
    simp\<close>

method assign\<^sub>\<C>_tac =
   wrap \<open>rule assign\<^sub>\<C>\<close>,
        simp,
       solves \<open>rule aexpr; simp\<close>, 
       (solves \<open>simp\<close>), 
      (solves \<open>simp\<close> | (clarsimp, fast)),
     (solves \<open>simp\<close>)?,
    simp

method if_tac 
  methods tac = 
  wrap \<open>rule if_type'\<close>, 
        solves \<open>rule bexpr, simp\<close>, 
       solves \<open>simp\<close>,
      solves \<open>tac\<close>, 
     solves \<open>tac\<close>, 
    solves \<open>clarsimp, fastforce\<close>

method has_type_no_if_tac' 
  declares aexpr bexpr= 
 (seq_tac \<open>call_by_name "has_type_no_if_tac'"\<close> |
   anno_tac \<open>call_by_name "has_type_no_if_tac'"\<close> |
   wrap \<open>rule skip_type\<close> | 
   wrap \<open>rule stop_type\<close> |
   assign\<^sub>1_tac| 
   assign\<^sub>2_tac | 
   assign\<^sub>\<C>_tac)?

method has_type_no_if_tac
  uses prog 
  declares aexpr bexpr = 
  (intro exI, unfold prog, has_type_no_if_tac')

method has_type_tac'
  declares aexpr bexpr= 
  (seq_tac \<open>call_by_name "has_type_tac'"\<close> |
   anno_tac \<open>call_by_name "has_type_tac'"\<close> |
   wrap \<open>rule skip_type\<close> | 
   wrap \<open>rule stop_type\<close> |
   assign\<^sub>2_tac |
   if_tac \<open>call_by_name "has_type_tac'"\<close> | 
   assign\<^sub>1_tac | 
   assign\<^sub>\<C>_tac)?




method has_type_tac uses prog declares aexpr bexpr = 
  (intro exI, unfold prog, has_type_tac')


method if_type_tac 
  declares bexpr custom_if =
   (wrap \<open>rule custom_if, 
            rule bexpr, 
           simp?, 
          simp?,
         has_type_tac', 
        has_type_tac', 
       (* 
        Check if this work for other cases? 
        If so just give the rest of this method a time out.
        Otherwise, remove from tac and add as explicit lemma proof *)
        (clarsimp simp: context_equiv_def type_equiv_def subtype_def)?,
       (clarsimp simp: context_equiv_def type_equiv_def subtype_def)?,
      (simp add: subset_entailment)?,
     (simp add: subset_entailment)?,
    (clarsimp,
    (subst tyenv_wellformed_def) ,
    (clarsimp simp: mds_consistent_def types_wellformed_def type_wellformed_def types_stable_def),
    (fastforce simp: tyenv_wellformed_def mds_consistent_def))?,
   (clarsimp,
   (subst tyenv_wellformed_def) ,
   (clarsimp simp: mds_consistent_def types_wellformed_def type_wellformed_def types_stable_def),
   (fastforce simp: tyenv_wellformed_def mds_consistent_def))?\<close>)


declaration \<open>fn phi => Context.mapping I (Data.put phi)\<close>


end

end
