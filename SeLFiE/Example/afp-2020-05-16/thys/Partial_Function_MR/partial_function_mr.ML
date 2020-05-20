(* Author: Rene Thiemann, License: LGPL *)

signature PARTIAL_FUNCTION_MR =
sig
  val init: string -> 
    (* make monad_map: monad term * funs * monad as typ * monad bs typ * a->b typs 
        -> map_monad funs monad term *)
    (term * term list * typ * typ * typ list -> term) -> 
    (* make monad type: fixed and flexible types *)
    (typ list * typ list -> typ) -> 
    (* destruct monad type: fixed and flexible types *)
    (typ -> typ list * typ list) -> 
    (* monad_map_compose thm: mapM f (mapM g x) = mapM (f o g) x *)
    thm list -> 
    (* monad_map_ident thm: mapM (% y. y) x = x *)
    thm list -> declaration

  val add_partial_function_mr: string -> (binding * typ option * mixfix) list ->
    Specification.multi_specs -> local_theory -> thm list * local_theory

  val add_partial_function_mr_cmd: string -> (binding * string option * mixfix) list ->
    Specification.multi_specs_cmd -> local_theory -> thm list * local_theory
end;


structure Partial_Function_MR: PARTIAL_FUNCTION_MR =
struct

val partial_function_mr_trace =
  Attrib.setup_config_bool @{binding partial_function_mr_trace} (K false);

fun trace ctxt msg =
  if Config.get ctxt partial_function_mr_trace 
  then tracing msg
  else ()

datatype setup_data = Setup_Data of 
 {mk_monad_map: term * term list * typ * typ * typ list -> term,
  mk_monadT: typ list * typ list -> typ,
  dest_monadT: typ -> typ list * typ list,
  monad_map_comp: thm list,
  monad_map_id: thm list};

(* the following code has been copied from partial_function.ML *)
structure Modes = Generic_Data
(
  type T = setup_data Symtab.table;
  val empty = Symtab.empty;
  val extend = I;
  fun merge data = Symtab.merge (K true) data;
)

val known_modes = Symtab.keys o Modes.get o Context.Proof;
val lookup_mode = Symtab.lookup o Modes.get o Context.Proof;

fun curry_const (A, B, C) =
  Const (@{const_name Product_Type.curry},
    [HOLogic.mk_prodT (A, B) --> C, A, B] ---> C);

fun mk_curry f =
  case fastype_of f of
    Type ("fun", [Type (_, [S, T]), U]) =>
      curry_const (S, T, U) $ f
  | T => raise TYPE ("mk_curry", [T], [f]);

fun curry_n arity = funpow (arity - 1) mk_curry;
fun uncurry_n arity = funpow (arity - 1) HOLogic.mk_case_prod;    
(* end copy of partial_function.ML *)

fun init mode mk_monad_map mk_monadT dest_monadT monad_map_comp monad_map_id phi =
  let
    val thm = Morphism.thm phi;
    (* TODO: are there morphisms required on mk_monad_map???, ... *)
    val data' = Setup_Data 
      {mk_monad_map=mk_monad_map, mk_monadT=mk_monadT, dest_monadT=dest_monadT, 
       monad_map_comp=map thm monad_map_comp,monad_map_id=map thm monad_map_id};
  in
    Modes.map (Symtab.update (mode, data'))
  end

fun mk_sumT (T1,T2) = Type (@{type_name sum}, [T1,T2])

fun mk_choiceT [ty] = ty
  | mk_choiceT (ty :: more) = mk_sumT (ty,mk_choiceT more) 
  | mk_choiceT _ = error "mk_choiceT []"

fun mk_choice_resT mk_monadT dest_monadT mTs = let
  val (commonTs,argTs) = map dest_monadT mTs |> split_list |> apfst hd;
  val n = length (hd argTs);
  val new = map (fn i => mk_choiceT (map (fn xs => nth xs i) argTs)) (0 upto (n - 1))
  in mk_monadT (commonTs,new) end;

fun mk_inj [_] t _ = t
  | mk_inj (ty :: more) t n = let
  val moreT = mk_choiceT more;
  val allT = mk_sumT (ty,moreT)
  in
    if n = 0 then Const (@{const_name Inl}, ty --> allT) $ t
    else Const (@{const_name Inr}, moreT --> allT) $ mk_inj more t (n-1)
  end
  | mk_inj _ _ _ = error "mk_inj [] _ _"

fun mk_proj [_] t _ = t
  | mk_proj (ty :: more) t n = let
  val moreT = mk_choiceT more;
  val allT = mk_sumT (ty,moreT)
  in
    if n = 0 then Const (@{const_name Sum_Type.projl}, allT --> ty) $ t
    else mk_proj more (Const (@{const_name Sum_Type.projr}, allT --> moreT) $ t) (n-1)
  end
  | mk_proj _ _ _ = error "mk_proj [] _ _"

fun get_head ctxt (_,(_,eqn)) =
  let
    val ((_, plain_eqn), _) = Variable.focus NONE eqn ctxt;
    val lhs = HOLogic.dest_eq (HOLogic.dest_Trueprop plain_eqn) |> #1;
    val head = strip_comb lhs |> #1;
  in 
    head 
  end;

fun get_infos lthy heads (fix,(_,eqn)) = let
    val ((_, plain_eqn), _) = Variable.focus NONE eqn lthy;
    val ((f_binding, fT), mixfix) = fix;
    val fname = Binding.name_of f_binding;
    val (lhs, rhs) = HOLogic.dest_eq (HOLogic.dest_Trueprop plain_eqn);
    val (_, args) = strip_comb lhs;
    val F = fold_rev lambda (heads @ args) rhs;
    val arity = length args;
    val (aTs, bTs) = chop arity (binder_types fT);    
    val tupleT = foldl1 HOLogic.mk_prodT aTs;
    val fT_uc = tupleT :: bTs ---> body_type fT;
    val (inT,resT) = dest_funT fT_uc;
    val f_uc = Free (fname, fT_uc);
    val f_cuc = curry_n arity f_uc
  in 
    (fname, f_cuc, f_uc, inT, resT, ((f_binding,mixfix),fT), F, arity, args)
  end;

fun fresh_var ctxt name = Name.variant name (Variable.names_of ctxt) |> #1

(* partial_function_mr definition *)
fun gen_add_partial_function_mr prep mode fixes_raw eqns_raw lthy =
  let
    val setup_data = the (lookup_mode lthy mode)
      handle Option.Option => error (cat_lines ["Unknown mode " ^ quote mode ^ ".",
        "Known modes are " ^ commas_quote (known_modes lthy) ^ "."]);
    val Setup_Data {mk_monad_map, mk_monadT, dest_monadT, monad_map_comp, monad_map_id} = setup_data;
    val _ = if length eqns_raw < 2 then error "require at least two function definitions" else ();
    val ((fixes, eq_abinding_eqns), _) = prep fixes_raw eqns_raw lthy;
    val _ = if length eqns_raw = length fixes then () else error "# of eqns does not match # of constants";
    val fix_eq_abinding_eqns = fixes ~~ eq_abinding_eqns;
    val heads = map (get_head lthy) fix_eq_abinding_eqns;
    val fnames = map (Binding.name_of o #1 o #1) fixes
    val fnames' = map (#1 o Term.dest_Free) heads
    val f_f = fnames ~~ fnames'
    val _ = case find_first (fn (f,g) => not (f = g)) f_f of NONE => () | SOME _ => 
      error ("list of function symbols does not match list of equations:\n" 
        ^ @{make_string} fnames ^ "\nvs\n" ^ @{make_string} fnames')
    val all = map (get_infos lthy heads) fix_eq_abinding_eqns
    val f_cucs = map #2 all
    val f_ucs = map #3 all
    val inTs = map #4 all
    val resTs = map #5 all
    val bindings_types = map #6 all
    val Fs = map #7 all
    val arities = map #8 all
    val all_args = map #9 all
    val glob_inT = mk_choiceT inTs
    val glob_resT = mk_choice_resT mk_monadT dest_monadT resTs
    val inj = mk_inj inTs
    val glob_fname = fresh_var lthy (foldl1 (fn (a,b) => a ^ "_" ^ b) (fnames @ [serial_string ()]))
    val glob_constT = glob_inT --> glob_resT;
    val glob_const = Free (glob_fname, glob_constT)
    val nums = 0 upto (length all - 1)
    fun mk_res_inj_proj n = let
        val resT = nth resTs n
        val glob_Targs = dest_monadT glob_resT |> #2
        val res_Targs = dest_monadT resT |> #2
        val m = length res_Targs
        fun inj_proj m = let
          val resTs_m = map (fn resT => nth (dest_monadT resT |> #2) m) resTs
          val resT_arg = nth resTs_m n
          val globT_arg = nth glob_Targs m
          val x = Free ("x",resT_arg)
          val y = Free ("x",globT_arg)
          val inj = lambda x (mk_inj resTs_m x n)
          val proj = lambda y (mk_proj resTs_m y n)
          in ((inj, resT_arg --> globT_arg), (proj, globT_arg --> resT_arg))
        end;
        val (inj,proj) = map inj_proj (0 upto (m - 1)) |> split_list
        val (t_to_ss_inj,t_to_sTs_inj) = split_list inj;
        val (t_to_ss_proj,t_to_sTs_proj) = split_list proj;
      in (fn mt => mk_monad_map (mt, t_to_ss_inj, resT, glob_resT, t_to_sTs_inj),
          fn mt => mk_monad_map (mt, t_to_ss_proj, glob_resT, resT, t_to_sTs_proj))
      end;
    val (res_inj, res_proj) = map mk_res_inj_proj nums |> split_list
    fun mk_global_fun n = let
        val fname = nth fnames n
        val inT = nth inTs n
        val xs = Free (fresh_var lthy ("x_" ^ fname), inT)
        val inj_xs = inj xs n
        val glob_inj_xs = glob_const $ inj_xs
        val glob_inj_xs_map = nth res_proj n glob_inj_xs 
        val res = lambda xs glob_inj_xs_map
      in 
        (xs,res)
      end
    val (xss,global_funs) = map mk_global_fun nums |> split_list
    fun mk_cases n = let
        val xs = nth xss n
        val F = nth Fs n;
        val arity = nth arities n;
        val F_uc =
          fold_rev lambda f_ucs (uncurry_n arity (list_comb (F, f_cucs)));
        val F_uc_inst = Term.betapplys (F_uc,global_funs)
        val res = lambda xs (nth res_inj n (F_uc_inst $ xs))
      in res end;
    val all_cases = map mk_cases nums;
    fun combine_cases [cs] [_] = cs
      | combine_cases (cs :: more) (inT :: moreTy) = 
          let
            val moreT = mk_choiceT moreTy
            val sumT = mk_sumT (inT, moreT)
            val case_const = Const 
              (@{const_name case_sum},
               (inT --> glob_resT) --> (moreT --> glob_resT) --> sumT --> glob_resT)        
          in case_const $ cs $ combine_cases more moreTy end
      | combine_cases _ _ = error "combine_cases with incompatible argument lists";
    val glob_x_name = fresh_var lthy ("x_" ^ glob_fname)
    val glob_x = Free (glob_x_name,glob_inT)
    val rhs = combine_cases all_cases inTs $ glob_x;
    val lhs = glob_const $ glob_x
    val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))
    val glob_binding = Binding.name (glob_fname) |> Binding.concealed
    val glob_attrib_binding = Binding.empty_atts
    val _ = trace lthy "invoking partial_function on global function"
    val priv_lthy = lthy
      |> Proof_Context.private_scope (Binding.new_scope())
    val ((glob_const, glob_simp_thm),priv_lthy') = priv_lthy
      |> Partial_Function.add_partial_function mode 
        [(glob_binding,SOME glob_constT,NoSyn)] (glob_attrib_binding,eq)
    val glob_lthy = priv_lthy' 
      |> Proof_Context.restore_naming lthy
    val _ = trace lthy "deriving simp rules for separate functions from global function"
    fun define_f n (fs, fdefs,rhss,lthy) = let
        val ((fbinding,mixfix),_) = nth bindings_types n
        val fname = nth fnames n
        val inT = nth inTs n;
        val arity = nth arities n;
        val x = Free (fresh_var lthy ("x_" ^ fname), inT)
        val inj_argsProd = inj x n
        val call = glob_const $ inj_argsProd
        val post = nth res_proj n call 
        val rhs = curry_n arity (lambda x post)
        val ((f, (_, f_def)),lthy') = 
          Local_Theory.define_internal ((fbinding,mixfix), (Binding.empty_atts, rhs)) lthy
      in 
        (f :: fs, f_def :: fdefs,rhs :: rhss,lthy')
      end
    val (fs,fdefs,f_rhss,local_lthy) = fold_rev define_f nums ([],[],[],glob_lthy) 
    val glob_simp_thm' = 
      let
        fun mk_case_new n = 
          let
            val F = nth Fs n
            val arity = nth arities n
            val Finst = uncurry_n arity (Term.betapplys (F,fs))
            val xs = nth xss n
            val res = lambda xs (nth res_inj n (Finst $ xs))
          in 
            res
          end;
        val new_cases = map mk_case_new nums;
        val rhs = combine_cases new_cases inTs $ glob_x;
        val lhs = glob_const $ glob_x
        val eq = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,rhs))
      in 
        Goal.prove local_lthy [glob_x_name] [] eq (fn {prems = _, context = ctxt} => 
            Thm.instantiate' [] [SOME (Thm.cterm_of ctxt glob_x)] glob_simp_thm
            |> (fn simp_thm => unfold_tac ctxt [simp_thm] THEN unfold_tac ctxt fdefs))
      end

    fun mk_simp_thm n = 
      let
        val args = nth all_args n
        val arg_names = map (dest_Free #> fst) args
        val f = nth fs n
        val F = nth Fs n
        val fdef = nth fdefs n
        val lhs = list_comb (f,args);
        val mhs = Term.betapplys (nth f_rhss n, args)
        val rhs = list_comb (list_comb (F,fs), args);
        val eq1 = HOLogic.mk_Trueprop (HOLogic.mk_eq (lhs,mhs))
        val eq2 = HOLogic.mk_Trueprop (HOLogic.mk_eq (mhs,rhs))      
        val simp_thm1 = Goal.prove local_lthy arg_names [] eq1 
          (fn {prems = _, context = ctxt} => unfold_tac ctxt [fdef])
  
        val simp_thm2 = Goal.prove local_lthy arg_names [] eq2 (fn {prems = _, context = ctxt} => 
            unfold_tac ctxt [glob_simp_thm']
            THEN unfold_tac ctxt @{thms sum.simps curry_def split}
            THEN unfold_tac ctxt (@{thm o_def} :: monad_map_comp)
            THEN unfold_tac ctxt (monad_map_id @ @{thms sum.sel}))        
      in 
        @{thm trans} OF [simp_thm1,simp_thm2]
      end
    val simp_thms = map mk_simp_thm nums
    fun register n lthy = 
      let
        val simp_thm = nth simp_thms n
        val eq_abinding = nth eq_abinding_eqns n |> fst
        val fname = nth fnames n
        val f = nth fs n
      in 
        lthy
        |> Local_Theory.note (eq_abinding, [simp_thm])
        |-> (fn (_, simps) => 
          Spec_Rules.add Binding.empty Spec_Rules.equational_recdef [f] simps
          #> Local_Theory.note 
            ((Binding.qualify true fname (Binding.name "simps"),
              @{attributes [code]}), simps) #>> snd #>> hd)
      end
  in 
    fold (fn i => fn (simps, lthy) => case register i lthy of
       (simp, lthy') => (simps @ [simp], lthy')) nums ([], local_lthy)
  end;

val add_partial_function_mr = gen_add_partial_function_mr Specification.check_multi_specs;
val add_partial_function_mr_cmd = gen_add_partial_function_mr Specification.read_multi_specs;

val mode = @{keyword "("} |-- Parse.name --| @{keyword ")"};

val _ =
  Outer_Syntax.local_theory @{command_keyword partial_function_mr} 
    "define mutually recursive partial functions"
    (mode -- Parse_Spec.specification
      >> (fn (mode, (fixes, specs)) => add_partial_function_mr_cmd mode fixes specs #> #2));

end
