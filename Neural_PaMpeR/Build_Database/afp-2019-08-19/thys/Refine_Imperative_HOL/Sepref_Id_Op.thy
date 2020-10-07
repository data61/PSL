section \<open>Operation Identification Phase\<close>
theory Sepref_Id_Op
imports 
  Main 
  Automatic_Refinement.Refine_Lib
  Automatic_Refinement.Autoref_Tagging
  "Lib/Named_Theorems_Rev"
begin

text \<open>
  The operation identification phase is adapted from the Autoref tool.
  The basic idea is to have a type system, which works on so called 
  interface types (also called conceptual types). Each conceptual type
  denotes an abstract data type, e.g., set, map, priority queue.
  
  Each abstract operation, which must be a constant applied to its arguments,
  is assigned a conceptual type. Additionally, there is a set of 
  {\emph pattern rewrite rules},
  which are applied to subterms before type inference takes place, and 
  which may be backtracked over. 
  This way, encodings of abstract operations in Isabelle/HOL, like 
  @{term [source] "\<lambda>_. None"} for the empty map, 
  or @{term [source] "fun_upd m k (Some v)"} for map update, can be rewritten
  to abstract operations, and get properly typed.
\<close>

subsection "Proper Protection of Term"
text \<open> The following constants are meant to encode abstraction and 
  application as proper HOL-constants, and thus avoid strange effects with
  HOL's higher-order unification heuristics and automatic 
  beta and eta-contraction.

  The first step of operation identification is to protect the term
  by replacing all function applications and abstractions be 
  the constants defined below.
\<close>

definition [simp]: "PROTECT2 x (y::prop) \<equiv> x"
consts DUMMY :: "prop"

abbreviation PROTECT2_syn ("'(#_#')") where "PROTECT2_syn t \<equiv> PROTECT2 t DUMMY"

abbreviation (input)ABS2 :: "('a\<Rightarrow>'b)\<Rightarrow>'a\<Rightarrow>'b" (binder "\<lambda>\<^sub>2" 10)
  where "ABS2 f \<equiv> (\<lambda>x. PROTECT2 (f x) DUMMY)"

lemma beta: "(\<lambda>\<^sub>2x. f x)$x \<equiv> f x" by simp

text \<open>
  Another version of @{const "APP"}. Treated like @{const APP} by our tool.
  Required to avoid infinite pattern rewriting in some cases, e.g., map-lookup.
\<close>

definition APP' (infixl "$''" 900) where [simp, autoref_tag_defs]: "f$'a \<equiv> f a"

text \<open>
  Sometimes, whole terms should be protected from being processed by our tool.
  For example, our tool should not look into numerals. For this reason,
  the \<open>PR_CONST\<close> tag indicates terms that our tool shall handle as
  atomic constants, an never look into them.

  The special form \<open>UNPROTECT\<close> can be used inside pattern rewrite rules.
  It has the effect to revert the protection from its argument, and then wrap
  it into a \<open>PR_CONST\<close>.
\<close>
definition [simp, autoref_tag_defs]: "PR_CONST x \<equiv> x" \<comment> \<open>Tag to protect constant\<close>
definition [simp, autoref_tag_defs]: "UNPROTECT x \<equiv> x" \<comment> \<open>Gets 
  converted to @{term PR_CONST}, after unprotecting its content\<close>


subsection \<open>Operation Identification\<close>

text \<open> Indicator predicate for conceptual typing of a constant \<close>
definition intf_type :: "'a \<Rightarrow> 'b itself \<Rightarrow> bool" (infix "::\<^sub>i" 10) where
  [simp]: "c::\<^sub>iI \<equiv> True"

lemma itypeI: "c::\<^sub>iI" by simp
lemma itypeI': "intf_type c TYPE('T)" by (rule itypeI)

lemma itype_self: "(c::'a) ::\<^sub>i TYPE('a)" by simp

definition CTYPE_ANNOT :: "'b \<Rightarrow> 'a itself \<Rightarrow> 'b" (infix ":::\<^sub>i" 10) where
  [simp]: "c:::\<^sub>iI \<equiv> c"

text \<open> Wrapper predicate for an conceptual type inference \<close>
definition ID :: "'a \<Rightarrow> 'a \<Rightarrow> 'c itself \<Rightarrow> bool" 
  where [simp]: "ID t t' T \<equiv> t=t'"

subsubsection \<open>Conceptual Typing Rules\<close>

lemma ID_unfold_vars: "ID x y T \<Longrightarrow> x\<equiv>y" by simp
lemma ID_PR_CONST_trigger: "ID (PR_CONST x) y T \<Longrightarrow> ID (PR_CONST x) y T" .

lemma pat_rule:
  "\<lbrakk> p\<equiv>p'; ID p' t' T \<rbrakk> \<Longrightarrow> ID p t' T" by simp

lemma app_rule:
  "\<lbrakk> ID f f' TYPE('a\<Rightarrow>'b); ID x x' TYPE('a)\<rbrakk> \<Longrightarrow> ID (f$x) (f'$x') TYPE('b)"
  by simp

lemma app'_rule:
  "\<lbrakk> ID f f' TYPE('a\<Rightarrow>'b); ID x x' TYPE('a)\<rbrakk> \<Longrightarrow> ID (f$'x) (f'$x') TYPE('b)"
  by simp

lemma abs_rule:
  "\<lbrakk> \<And>x x'. ID x x' TYPE('a) \<Longrightarrow> ID (t x) (t' x x') TYPE('b) \<rbrakk> \<Longrightarrow>
    ID (\<lambda>\<^sub>2x. t x) (\<lambda>\<^sub>2x'. t' x' x') TYPE('a\<Rightarrow>'b)"
  by simp

lemma id_rule: "c::\<^sub>iI \<Longrightarrow> ID c c I" by simp

lemma annot_rule: "ID t t' I \<Longrightarrow> ID (t:::\<^sub>iI) t' I"
  by simp

lemma fallback_rule:
  "ID (c::'a) c TYPE('c)"
  by simp

lemma unprotect_rl1: "ID (PR_CONST x) t T \<Longrightarrow> ID (UNPROTECT x) t T"
  by simp

subsection \<open> ML-Level code \<close>
ML \<open>
infix 0 THEN_ELSE_COMB'

signature ID_OP_TACTICAL = sig
  val SOLVE_FWD: tactic' -> tactic'
  val DF_SOLVE_FWD: bool -> tactic' -> tactic'
end

structure Id_Op_Tactical :ID_OP_TACTICAL = struct

  fun SOLVE_FWD tac i st = SOLVED' (
    tac 
    THEN_ALL_NEW_FWD (SOLVE_FWD tac)) i st


  (* Search for solution with DFS-strategy. If dbg-flag is given,
    return sequence of stuck states if no solution is found.
  *)
  fun DF_SOLVE_FWD dbg tac = let
    val stuck_list_ref = Unsynchronized.ref []

    fun stuck_tac _ st = if dbg then (
      stuck_list_ref := st :: !stuck_list_ref;
      Seq.empty
    ) else Seq.empty

    fun rec_tac i st = (
        (tac THEN_ALL_NEW_FWD (SOLVED' rec_tac))
        ORELSE' stuck_tac
      ) i st

    fun fail_tac _ _ = if dbg then
      Seq.of_list (rev (!stuck_list_ref))
    else Seq.empty
  in
    rec_tac ORELSE' fail_tac    
  end

end
\<close>


named_theorems_rev id_rules "Operation identification rules"
named_theorems_rev pat_rules "Operation pattern rules"
named_theorems_rev def_pat_rules "Definite operation pattern rules (not backtracked over)"



ML \<open>

  structure Id_Op = struct

    fun id_a_conv cnv ct = case Thm.term_of ct of
      @{mpat "ID _ _ _"} => Conv.fun_conv (Conv.fun_conv (Conv.arg_conv cnv)) ct
    | _ => raise CTERM("id_a_conv",[ct])

    fun 
      protect env (@{mpat "?t:::\<^sub>i?I"}) = let
        val t = protect env t
      in 
        @{mk_term env: "?t:::\<^sub>i?I"}
      end
    | protect _ (t as @{mpat "PR_CONST _"}) = t
    | protect env (t1$t2) = let
        val t1 = protect env t1
        val t2 = protect env t2
      in
        @{mk_term env: "?t1.0 $ ?t2.0"}
      end
    | protect env (Abs (x,T,t)) = let
        val t = protect (T::env) t
      in
        @{mk_term env: "\<lambda>v_x::?'v_T. PROTECT2 ?t DUMMY"}
      end
    | protect _ t = t

    fun protect_conv ctxt = Refine_Util.f_tac_conv ctxt
      (protect []) 
      (simp_tac 
        (put_simpset HOL_basic_ss ctxt addsimps @{thms PROTECT2_def APP_def}) 1)

    fun unprotect_conv ctxt
      = Simplifier.rewrite (put_simpset HOL_basic_ss ctxt 
        addsimps @{thms PROTECT2_def APP_def})

    fun do_unprotect_tac ctxt =
      resolve_tac ctxt @{thms unprotect_rl1} THEN'
      CONVERSION (Refine_Util.HOL_concl_conv (fn ctxt => id_a_conv (unprotect_conv ctxt)) ctxt)

    val cfg_id_debug = 
      Attrib.setup_config_bool @{binding id_debug} (K false)

    val cfg_id_trace_fallback = 
      Attrib.setup_config_bool @{binding id_trace_fallback} (K false)

    fun dest_id_rl thm = case Thm.concl_of thm of
      @{mpat (typs) "Trueprop (?c::\<^sub>iTYPE(?'v_T))"} => (c,T)
    | _ => raise THM("dest_id_rl",~1,[thm])

    
    val add_id_rule = snd oo Thm.proof_attributes [Named_Theorems_Rev.add @{named_theorems_rev id_rules}]

    datatype id_tac_mode = Init | Step | Normal | Solve

    fun id_tac ss ctxt = let
      open Id_Op_Tactical
      val certT = Thm.ctyp_of ctxt
      val cert = Thm.cterm_of ctxt

      val thy = Proof_Context.theory_of ctxt

      val id_rules = Named_Theorems_Rev.get ctxt @{named_theorems_rev id_rules}
      val pat_rules = Named_Theorems_Rev.get ctxt @{named_theorems_rev pat_rules}
      val def_pat_rules = Named_Theorems_Rev.get ctxt @{named_theorems_rev def_pat_rules}

      val rl_net = Tactic.build_net (
        (pat_rules |> map (fn thm => thm RS @{thm pat_rule})) 
        @ @{thms annot_rule app_rule app'_rule abs_rule} 
        @ (id_rules |> map (fn thm => thm RS @{thm id_rule}))
      )

      val def_rl_net = Tactic.build_net (
        (def_pat_rules |> map (fn thm => thm RS @{thm pat_rule}))
      )  

      val id_pr_const_rename_tac = 
          resolve_tac ctxt @{thms ID_PR_CONST_trigger} THEN'
          Subgoal.FOCUS (fn { context=ctxt, prems, ... } => 
            let
              fun is_ID @{mpat "Trueprop (ID _ _ _)"} = true | is_ID _ = false
              val prems = filter (Thm.prop_of #> is_ID) prems
              val eqs = map (fn thm => thm RS @{thm ID_unfold_vars}) prems
              val conv = Conv.rewrs_conv eqs
              val conv = fn ctxt => (Conv.top_sweep_conv (K conv) ctxt)
              val conv = fn ctxt => Conv.fun2_conv (Conv.arg_conv (conv ctxt))
              val conv = Refine_Util.HOL_concl_conv conv ctxt
            in CONVERSION conv 1 end 
          ) ctxt THEN'
          resolve_tac ctxt @{thms id_rule} THEN'
          resolve_tac ctxt id_rules 

      val ityping = id_rules 
        |> map dest_id_rl
        |> filter (is_Const o #1)
        |> map (apfst (#1 o dest_Const))
        |> Symtab.make_list

      val has_type = Symtab.defined ityping

      fun mk_fallback name cT =
        case try (Sign.the_const_constraint thy) name of
          SOME T => try (Thm.instantiate' 
                          [SOME (certT cT), SOME (certT T)] [SOME (cert (Const (name,cT)))])
                        @{thm fallback_rule} 
        | NONE => NONE

      fun trace_fallback thm = 
        Config.get ctxt cfg_id_trace_fallback       
        andalso let 
          open Pretty
          val p = block [str "ID_OP: Applying fallback rule: ", Thm.pretty_thm ctxt thm]
        in 
          string_of p |> tracing; 
          false
        end  

      val fallback_tac = CONVERSION Thm.eta_conversion THEN' IF_EXGOAL (fn i => fn st =>
        case Logic.concl_of_goal (Thm.prop_of st) i of
          @{mpat "Trueprop (ID (mpaq_STRUCT (mpaq_Const ?name ?cT)) _ _)"} => (
            if not (has_type name) then 
              case mk_fallback name cT of
                SOME thm => (trace_fallback thm; resolve_tac ctxt [thm] i st)
              | NONE => Seq.empty  
            else Seq.empty
          )
        | _ => Seq.empty)

      val init_tac = CONVERSION (
        Refine_Util.HOL_concl_conv (fn ctxt => (id_a_conv (protect_conv ctxt))) 
          ctxt
      )

      val step_tac = (FIRST' [
        assume_tac ctxt, 
        eresolve_tac ctxt @{thms id_rule},
        resolve_from_net_tac ctxt def_rl_net, 
        resolve_from_net_tac ctxt rl_net, 
        id_pr_const_rename_tac,
        do_unprotect_tac ctxt, 
        fallback_tac])

      val solve_tac = DF_SOLVE_FWD (Config.get ctxt cfg_id_debug) step_tac  

    in
      case ss of
        Init => init_tac 
      | Step => step_tac 
      | Normal => init_tac THEN' solve_tac
      | Solve => solve_tac

    end

  end

\<close>

subsection \<open>Default Setup\<close>

subsubsection \<open>Numerals\<close> 
lemma pat_numeral[def_pat_rules]: "numeral$x \<equiv> UNPROTECT (numeral$x)" by simp

lemma id_nat_const[id_rules]: "(PR_CONST (a::nat)) ::\<^sub>i TYPE(nat)" by simp
lemma id_int_const[id_rules]: "(PR_CONST (a::int)) ::\<^sub>i TYPE(int)" by simp

(*subsection \<open>Example\<close>
schematic_lemma 
  "ID (\<lambda>a b. (b(1::int\<mapsto>2::nat) |`(-{3})) a, Map.empty, \<lambda>a. case a of None \<Rightarrow> Some a | Some _ \<Rightarrow> None) (?c) (?T::?'d itself)"
  (*"TERM (?c,?T)"*)
  using [[id_debug]]
  apply (tactic {* Id_Op.id_tac Id_Op.Normal @{context} 1  *})  
  done
*)

end

