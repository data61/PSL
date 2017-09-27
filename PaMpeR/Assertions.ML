(*  Title:      Assertions.ML
    Author:     Yilun He, Data61, CSIRO
                Yutaka Nagashima, CIIRC, CTU
    
    This file stores the written assertions, which
    can be used to extract features from proof state.

    eval_assertion converts a proof state to a list of real values, which is the feature vector of
    the state.

    User can add their own assertion as functions (thm, context) -> boolean
*)

signature ASSERTIONS =
sig
  (*  written assertions  *)
  val eval_assertion: Proof.state -> real list
end;

(*** Implementation of assertions ***)
structure Assertions =
struct
(**  Generic utility and assertion functions  **)

fun if_solved (goal:thm) then_clause else_clause =
  if Thm.nprems_of goal = 0 then then_clause else else_clause;
val prems_of  = Thm.prems_of;

(* returns some constant that meet given criteria *)
fun const_list (goal:thm) = if_solved goal [] (Term.add_const_names (prems_of goal |> hd) []);

fun const_exist_assert goal (f:string -> bool) = 
  let 
    fun exist (str,_) = f str
  in
    Term.exists_Const exist (prems_of goal |> hd)
  end;

(* All constant meet given criteria *)
fun const_all_assert goal (f:string -> bool) = 
  let 
    fun all_const (str::strs) = f str andalso all_const strs
     |  all_const [] = true
  in
    all_const (const_list goal) 
  end;

(* dead code? *)
fun trace_list (x::xs) = (tracing x; trace_list xs)
  | trace_list [] = ();

(* gets the thms that are named after a given constant with a given suffix from the current context. *)
fun get_thms_of_const_name_with_suffix (ctxt:Proof.context) (sfx:string) (cname:string) =
  try (Proof_Context.get_thms ctxt) (cname ^ "." ^ sfx) |> these:thm list;

(* checks if the current constant contains thms that are named after a given constant with a given suffix. *)
fun has_thms_of_const_name_with_suffix (ctxt:Proof.context) (sfx:string) (cname:string) =
  get_thms_of_const_name_with_suffix ctxt sfx cname |> null |> not:bool;

(* similar to get_thms_of_const_name_with_suffix, but with multiple constant names. *)
fun get_thms_of_const_names_with_suffix (ctxt:Proof.context) (cnames:string list) (sfx:string) =
  map (get_thms_of_const_name_with_suffix ctxt sfx) cnames |> flat:thm list;

(* similar to has_thms_of_const_name_with_suffix, but with multiple constant names. *)
fun has_thms_of_const_names_with_suffix (ctxt:Proof.context) (cnames:string list) (sfx:string) =
  exists (has_thms_of_const_name_with_suffix ctxt sfx) cnames:bool;

(* checks if the context contains thms that are named after a constant in the goal but with one of the given suffixes. *)
fun has_thms_with_suffixes (goal:thm) (ctxt:Proof.context) (sfxes:string list) =
  let
    val const_names = Isabelle_Utils.get_const_names_in_1st_subg goal;
    val has_thms    = exists (has_thms_of_const_names_with_suffix ctxt const_names) sfxes;
  in has_thms end:bool;

(** Used Assertions **)

(* Constant name related assertion:  set prefix const *)
(* Using factassert: set prefix fact *)
(* Other assertion, or complex ones : set prefix "check" *)

(* check if proof context contains local assumption *)
fun check_local_assms _ ctxt = ctxt
  |> Proof_Context.theory_of
  |> Proof_Context.init_global
  |> Assumption.local_assms_of ctxt
  |> null
  |> not

(* check if proof subgoal contains case declaration *)
fun const_case goal _ =
  let 
     fun is_case cons_name = String.isSubstring "case_" cons_name;
  in
     if_solved goal false (const_exist_assert goal is_case)
  end

(* check if the outermost constant in subgoal is conjunction *)
fun const_conj goal _ =
  let
    val fst_subg = prems_of goal |> hd;
    val tail = Isabelle_Utils.flatten_trm fst_subg |> tl;
    fun check_empty []     = NONE
     |  check_empty (x::_) = SOME x
    val head = check_empty tail
    fun isconj (SOME (Term.Const ("HOL.conj",_)))         = true
     |  isconj (SOME (Term.Const ("Pure.conjuncion", _))) = true
     |  isconj  _                                         = false
  in
    isconj head
  end;

(* check if the subgoal contains constant "for all" *)
fun const_all goal _ = 
  let
    fun is_all cons_name = (cons_name = "Pure.all")
  in
    const_exist_assert goal is_all
  end;

(* check if the constants have affiliated facts with following suffices *)
fun fact_pinduct goal ctxt = has_thms_with_suffixes goal ctxt ["pinduct"]
fun fact_psimp   goal ctxt = has_thms_with_suffixes goal ctxt ["psimp"]
fun fact_pelims  goal ctxt = has_thms_with_suffixes goal ctxt ["pelims"]
fun fact_cases   goal ctxt = has_thms_with_suffixes goal ctxt ["cases"]
fun fact_intros  goal ctxt = has_thms_with_suffixes goal ctxt ["intros"]

(* check if the constants in the current proof goal has a recursive simp rule *)
fun check_rec_simp goal ctxt =
  let
    val const_names = if_solved goal [] (Term.add_const_names (prems_of goal |> hd) []);
    fun isrec (_ $ (Term.Const ("HOL.eq",_)$A$B)) name = Term.exists_Const (fn (s,_) => name=s) A
                                              andalso Term.exists_Const (fn (s,_) => name=s) B|
        isrec _ _= false
    fun check_thm_list (t::ts) q = isrec (Thm.concl_of t) q orelse check_thm_list ts q|
        check_thm_list [] _ = false
    fun findfact (name::namelist) = (check_thm_list (Proof_Context.get_thms ctxt (name^".simps")) name
                              handle ERROR _ => findfact namelist)|
        findfact [] = false
  in findfact const_names
  end;

(* check if there is a constant with prefix num *)
fun const_num goal _ =
  let
    fun isNum str = (Long_Name.explode str |> hd handle Empty => "") = "Num";
  in
    const_exist_assert goal isNum
  end

(* check if the context have facts with suffix corresponding to lift_definition*)
fun fact_lift_def goal ctxt =
  let
    val lift_lemmas = ["abs_eq","rsp","transfer","rep_eq"]
  in
    has_thms_with_suffixes goal ctxt lift_lemmas
  end

(* Check for definition lemmas of primcorec *)
fun fact_primcorec goal ctxt = has_thms_with_suffixes goal ctxt ["code","ctr","sel"];

(* Check for definition lemmas of interpretation *)
fun fact_interp goal ctxt = has_thms_with_suffixes goal ctxt ["cfg_axioms","weakGreibach"];

(* check if the outermost constant is a function *)
fun check_outer_const goal _ =
  let
    val t    = prems_of goal |>hd;
    val tail = Isabelle_Utils.flatten_trm t |>tl handle Empty => [];
    fun check_empty []     = NONE
     |  check_empty (x::_) = SOME x
    val head = check_empty tail
    fun isfun (SOME (Term.Const (_,typ))) = (Term.size_of_typ typ)> 1|
        isfun _ = false
  in
    isfun head
  end;

(** the list of assertions currently used **)
val assertions =
(*01*) [check_local_assms,
(*02*)  const_case,
(*03*)  const_conj,
(*04*)  const_all,
(*05*)  fact_pinduct,
(*06*)  fact_psimp,
(*07*)  fact_pelims,
(*08*)  fact_cases,
(*09*)  fact_intros,
(*10*)  check_rec_simp,
(*11*)  const_num,
(*12*)  fact_lift_def,
(*13*)  fact_primcorec,
(*14*)  fact_interp,
(*15*)  check_outer_const]

(** assertions not used currently **)
(* check if all constants are defined in Main *)
fun const_main (goal, ctxt)=
  let
    val main_list = Theory.ancestors_of (Context.get_theory (Proof_Context.theory_of ctxt) "Main") |> map Context.theory_name
    fun inMain str = exists (fn s => s = (Long_Name.explode str|> hd)) main_list
  in
    const_all_assert goal inMain
  end

(* check if there is a constant with prefix real *)
fun const_real (goal, _) = 
  let
    fun isReal str = (Long_Name.explode str |> hd handle Empty => "") = "Real";
  in
    const_exist_assert goal isReal
  end
(** Function used to generate database **)

(* Parse the argument of command by/apply into the name of method*)
fun get_name (Method.Source src) = (Token.name_of_src src |> fst) (*
                                  ^" "^          
                                  (*this part add the argument of applied method*)
                                  (space_implode "" (map Token.content_of (Token.args_of_src src))) *)
 |  get_name _ = ""

(* evaluate assertions and return a string for generating/matching database*)
fun eval_assertion_gen (state:Proof.state) (assrts:(thm -> Proof.context -> bool) list) =
    let
      val {goal:thm, context:Proof.context, facts:thm list} = Proof.goal state;
      val fvector = if_solved goal [] (Utils.map_arg (goal, context) (map uncurry assrts));
    in
      fvector : bool list
    end;

fun eval_assertion state = eval_assertion_gen state assertions |> map Utils.bool_to_real: real list

end;
