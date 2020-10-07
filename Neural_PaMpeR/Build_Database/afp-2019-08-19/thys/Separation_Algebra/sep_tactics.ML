(* Title: Tactics for abstract separation algebras
   Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

(* Separating Conjunction (and Top, AKA sep_true) {{{

  This defines all the constants and theorems necessary for the conjunct
  selection and cancelling tactic, as well as utility functions.
*)

structure SepConj =
struct

val sep_conj_term = @{term sep_conj};
val sep_conj_str = "**";
val sep_conj_ac = @{thms sep_conj_ac};
val sep_conj_impl = @{thm sep_conj_impl}

fun is_sep_conj_const (Const (@{const_name sep_conj}, _)) = true
  | is_sep_conj_const _ = false;

fun is_sep_conj_term
      (Const t $ _ $ _ $ _) = is_sep_conj_const (Const t)
  | is_sep_conj_term _ = false;

fun is_sep_conj_prop
      (Const Trueprop $ t) = is_sep_conj_term t
  | is_sep_conj_prop _ = false;

fun break_sep_conj (Const (@{const_name sep_conj},_) $ t1 $ t2 $ _) =
  [t1] @ (break_sep_conj t2)
  | break_sep_conj (Const (@{const_name sep_conj},_) $ t1 $ t2) =
  [t1] @ (break_sep_conj t2)
  (* dig through eta exanded terms: *)
  | break_sep_conj (Abs (_, _, t $ Bound 0)) = break_sep_conj t
  | break_sep_conj t = [t];

fun is_sep_true_term (Abs (_, _, Const (@{const_name True}, _))) = true
  | is_sep_true_term _ = false;

end;

(* }}} *)

(* Convenience functions for lists {{{ *)
structure ListExtra =
struct

fun init l = List.take (l, List.length l - 1);

fun range _ 0 = []
  | range from howmany = from :: (range (from+1) (howmany-1));

(* move nth element in list to the front *)
fun nth_to_front i xs =
      (nth xs i) :: (List.take (xs, i)) @ (List.drop (xs,i+1));

(* assign all members of list an index in the list *)
fun index_list xs = ListPair.zip (range 0 (length xs), xs);

end; (* }}} *)

(* Function application terms {{{ *)
(* Dealing with function applications of the type
     Const/Free(name,type) $ arg1 $ arg2 $ ... $ last_arg *)
structure FunApp =
struct

(* apply a transformation to the args in a function application term *)
fun app_args_op f t = strip_comb t |> apsnd f |> list_comb;

(* remove last argument *)
fun app_del_last_arg t = app_args_op ListExtra.init t;

(* apply a function term to a Free with given name *)
fun fun_app_free t free_name = t $ Free (free_name, type_of t |> domain_type);

(* fold two-argument function over a list of arg names using fun_app_free *)
fun fun_app_foldr f [a,b] = fun_app_free (fun_app_free f a) b
  | fun_app_foldr f (x::xs) = (fun_app_free f x) $ (fun_app_foldr f xs)
  | fun_app_foldr _ _ = raise Fail "fun_app_foldr";

end; (* }}} *)

(* Selecting Conjuncts in Premise or Conclusion {{{ *)

(* Constructs a rearrangement lemma of the kind:
   (A ** B ** C) s ==> (C ** A ** B) s
   When cjt_select = 2 (0-based index of C) and
   cjt_select = 3 (number of conjuncts to use), conclusion = true
   "conclusion" specifies whether the rearrangement occurs in conclusion
   (for dtac) or the premise (for rtac) of the rule.
*)
fun mk_sep_select_rule ctxt conclusion (cjt_count, cjt_select) =
let
  fun variants nctxt names = fold_map Name.variant names nctxt;

  val (state, nctxt0) = Name.variant "s" (Variable.names_of ctxt);
  fun sep_conj_prop cjts =
        FunApp.fun_app_free
          (FunApp.fun_app_foldr SepConj.sep_conj_term cjts) state
        |> HOLogic.mk_Trueprop;

  (* concatenate string and string of an int *)
  fun conc_str_int str int = str ^ Int.toString int;

  (* make the conjunct names *)
  val (cjts, _) = ListExtra.range 1 cjt_count
                  |> map (conc_str_int "a") |> variants nctxt0;

  (* make normal-order separation conjunction terms *)
  val orig = sep_conj_prop cjts;

  (* make reordered separation conjunction terms *)
  val reordered = sep_conj_prop (ListExtra.nth_to_front cjt_select cjts);

  val goal = Logic.mk_implies
               (if conclusion then (orig, reordered) else (reordered, orig));

  (* simp add: sep_conj_ac *)
  val sep_conj_ac_tac = Simplifier.asm_full_simp_tac
                          (put_simpset HOL_basic_ss ctxt addsimps SepConj.sep_conj_ac);

in
  (* XXX: normally you'd want to keep track of what variables we want to make
     schematic and which ones are bound, but we don't use fixed names for
     the rules we make, so we use Drule.export_without_context to schematise
     all. *)
  Goal.prove ctxt [] [] goal (fn _ => sep_conj_ac_tac 1)
  |> Drule.export_without_context
end;

(* }}} *)

local
  (* Common tactic functionality {{{ *)

  (* given two terms of some 'a to bool, can you prove
     \<And>s. t1 s \<Longrightarrow> t2 s
     using the supplied proof method?
     NOTE: t1 and t2 MUST have a function type with one argument,
     or TYPE dest_Type is raised
     NOTE: if asm or concl is sep_true, returns false
  *)
  fun can_prove ctxt tac asm concl =
    let
      fun variant name = Name.variant name (Variable.names_of ctxt) |> fst;
      val arg_name = variant "s";
      val left = FunApp.fun_app_free asm arg_name |> HOLogic.mk_Trueprop;
      val right = FunApp.fun_app_free concl arg_name |> HOLogic.mk_Trueprop;
      val goal = Logic.mk_implies (left, right);
    in
      if (SepConj.is_sep_true_term asm) orelse (SepConj.is_sep_true_term concl)
      then false
      else (Goal.prove ctxt [] [] goal (fn _ => tac 1); true)
            handle ERROR _ => false
    end;

  (* apply function in list until it returns SOME *)
  fun find_some (x::xs) f =
    (case f x of SOME v => SOME v
               | NONE => find_some xs f)
    | find_some [] _ = NONE;

  (* Given indices into the separating conjunctions in the assumption and
     conclusion, rewrite them so that the targeted conjuncts are at the
     front, then remove them. *)
  fun eliminate_target_tac ctxt tac
                           ((prem_total,prem_idx), (concl_total,concl_idx)) =
    let
      val asm_select = mk_sep_select_rule ctxt true (prem_total,prem_idx);
      val concl_select = mk_sep_select_rule ctxt false
                           (concl_total,concl_idx);
    in
      dresolve_tac ctxt [asm_select] THEN'
      resolve_tac ctxt [concl_select] THEN'
      eresolve_tac ctxt [SepConj.sep_conj_impl] THEN' tac
    end;

  fun find_target ctxt tac cprem cconcl =
    let
      val prem_cjts = cprem |> Thm.term_of |> SepConj.break_sep_conj;
      val concl_cjts = cconcl |> Thm.term_of |> SepConj.break_sep_conj;

      val iprems = ListExtra.index_list prem_cjts;
      val iconcls = ListExtra.index_list concl_cjts;

      fun can_prove' (pi,p) (ci,c) =
            if can_prove ctxt tac p c then SOME (pi, ci) else NONE;

      val target = find_some iconcls
                     (fn c => find_some iprems (fn p => can_prove' p c));
    in
      case target
        of SOME (pi,ci) => SOME ((List.length prem_cjts, pi),
                                 (List.length concl_cjts, ci))
         | NONE => NONE
    end;

  fun strip_cprop ct = (HOLogic.dest_Trueprop (Thm.term_of ct); Thm.dest_arg ct);

  (* }}} *)
in

  (* Tactic: Select nth conjunct in assumption {{{ *)
  local
    fun sep_select_asm_tac' ctxt n (ct, i) =
      let
        (* digging out prems *)
        val ((_, ct'), _) = Variable.focus_cterm NONE ct ctxt;
        val prems = Drule.strip_imp_prems ct';

        fun prem_ok ct = SepConj.is_sep_conj_prop (Thm.term_of ct)

        fun mk_tac prem =
            let
              val prem = HOLogic.dest_Trueprop (Thm.term_of prem)
              val p = length (SepConj.break_sep_conj prem)
              val th = mk_sep_select_rule ctxt true (p,n)
                  handle Subscript => error "Conjunct index out of range"
             in
               dresolve_tac ctxt [th] i
             end;
      in
        if length prems = 0
        then error ("No assumption of form: (_ " ^ SepConj.sep_conj_str ^
                    " _) _")
        else
          (* backtrack until first premise that does something *)
          map mk_tac (filter prem_ok prems) |> FIRST
      end;
    in
      fun sep_select_asm_tac ctxt n = CSUBGOAL (sep_select_asm_tac' ctxt (n-1))
    end; (* }}} *)

  (* Tactic: Select nth conjunct in conclusion {{{ *)
  local
    fun sep_select_tac' ctxt n (ct, i) =
      let
        (* digging out conclusions *)
        val ((_, ct'), _) = Variable.focus_cterm NONE ct ctxt;
        val concl = ct' |> Drule.strip_imp_concl |> Thm.term_of;
        val p = concl |> HOLogic.dest_Trueprop |> SepConj.break_sep_conj
                |> length;
        val th = mk_sep_select_rule ctxt false (p,n)
                 handle Subscript => error "Conjunct index out of range"
      in
        if not (SepConj.is_sep_conj_prop concl)
        then error ("Goal not of form: (_ " ^ SepConj.sep_conj_str ^ " _) _")
        else resolve_tac ctxt [th] i
      end;
  in
    fun sep_select_tac ctxt n = CSUBGOAL (sep_select_tac' ctxt (n-1))
  end; (* }}} *)

  (* Tactic: for all reorderings of the premises try apply tac {{{ *)
    local
      fun sep_assm_tac' ctxt tac (ct,i) =
        let
          (* digging out prems *)
          val ((_, ct'), _) = Variable.focus_cterm NONE ct ctxt;
          val prems = Drule.strip_imp_prems ct';

          fun prem_ok ct = SepConj.is_sep_conj_prop (Thm.term_of ct)

          fun mk_tac prem =
            let
              val prem = HOLogic.dest_Trueprop (Thm.term_of prem)
              val p = length (SepConj.break_sep_conj prem)
              fun ord n = mk_sep_select_rule ctxt true (p,n)
              val ord_thms = map ord (0 upto p-1)
            in
                (dresolve_tac ctxt ord_thms THEN' tac) i
            end;
        in
          (* backtrack until first premise that does something *)
          map mk_tac (filter prem_ok prems) |> FIRST
        end;
    in
      fun sep_assm_tac ctxt tac = CSUBGOAL (sep_assm_tac' ctxt tac)
    end; (* }}} *)

  (* Tactic: for all reorderings of the conclusion, try apply tac {{{ *)
  local
    fun sep_concl_tac' ctxt tac (ct, i) =
      let
        (* digging out conclusion *)
        val ((_, ct'), _) = Variable.focus_cterm NONE ct ctxt;
        val concl = ct' |> Drule.strip_imp_concl |> Thm.term_of;
        val p = concl |> HOLogic.dest_Trueprop |> SepConj.break_sep_conj
                |> length;
        fun ord n = mk_sep_select_rule ctxt false (p,n);
        val ord_thms = map ord (0 upto p-1);
      in
        if not (SepConj.is_sep_conj_prop concl)
        then (tracing ("Goal not of form: (_ " ^ SepConj.sep_conj_str ^
                      " _) _");
              no_tac)
        else (resolve_tac ctxt ord_thms THEN' tac) i
      end;
  in
    fun sep_concl_tac ctxt tac = CSUBGOAL (sep_concl_tac' ctxt tac)
  end; (* }}} *)

  (* Tactic: Cancel conjuncts of assumption and conclusion via tac {{{ *)
  local
    fun sep_cancel_tac' ctxt tac (ct, i) =
      let
        (* digging out prems and conclusions *)
        val ((vars, ct'), ctxt') = Variable.focus_cterm NONE ct ctxt;
        val concl = Drule.strip_imp_concl ct';
        val prems = Drule.strip_imp_prems ct';

        fun prem_ok ct =
          let
            (* name of state in sep conj (should be Free after focus) *)
            fun state_get (_ $ _ $ _ $ s) = s
              | state_get t = raise Fail "prem_ok: state_get";
            val state_get_ct = state_get o HOLogic.dest_Trueprop o Thm.term_of;

            val concl_state = concl |> state_get_ct;
            (* states considered equal if they alpha-convert *)
            fun state_ok ct = (state_get_ct ct) aconv concl_state;
          in
            SepConj.is_sep_conj_prop (Thm.term_of ct) andalso state_ok ct
          end;

        fun mk_tac prem =
              case find_target ctxt tac (prem |> strip_cprop)
                                        (strip_cprop concl)
                of SOME target => eliminate_target_tac ctxt tac target i
                 | NONE => no_tac;
      in
        if (not (concl |> Thm.term_of |> SepConj.is_sep_conj_prop))
        then (tracing ("Goal not of form: (_ " ^ SepConj.sep_conj_str ^
                       " _) _");
              no_tac)
        else if (length prems = 0)
        then (tracing ("No assumption of form: (_ " ^ SepConj.sep_conj_str ^
                       " _) _");
              no_tac)
        else
          (* backtrack until first premise that does something *)
          map mk_tac (filter prem_ok prems) |> FIRST
      end;
  in
    fun sep_cancel_tac ctxt tac = CSUBGOAL (sep_cancel_tac' ctxt tac)
  end;
  (* }}} *)

  (* Derived Tactics *)

  fun sep_atac ctxt = sep_assm_tac ctxt (assume_tac ctxt);

  (* Substitution *)
  fun sep_subst_tac ctxt occs thms =
        EqSubst.eqsubst_tac ctxt occs thms THEN' sep_atac ctxt;
  fun sep_subst_asm_tac ctxt occs thms =
        EqSubst.eqsubst_asm_tac ctxt occs thms THEN' sep_atac ctxt;

  (* Forward reasoning *)
  fun sep_dtac ctxt thms = sep_assm_tac ctxt (dresolve_tac ctxt thms)
  fun sep_ftac ctxt thms = sep_assm_tac ctxt (forward_tac ctxt thms)

  (* Backward reasoning *)
  fun sep_rtac ctxt thms = sep_concl_tac ctxt (resolve_tac ctxt thms)

end;

(* vim: set foldmethod=marker sw=2 sts=2 et: *)

