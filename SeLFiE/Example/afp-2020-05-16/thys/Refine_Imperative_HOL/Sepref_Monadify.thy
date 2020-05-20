section \<open>Monadify\<close>
theory Sepref_Monadify
imports Sepref_Basic Sepref_Id_Op
begin


text \<open>
  In this phase, a monadic program is converted to complete monadic form,
  that is, computation of compound expressions are made visible as top-level 
  operations in the monad.

  The monadify process is separated into 2 steps.
  \begin{enumerate}
    \item In a first step, eta-expansion is used to add missing operands 
      to operations and combinators. This way, operators and combinators
      always occur with the same arity, which simplifies further processing.

    \item In a second step, computation of compound operands is flattened,
      introducing new bindings for the intermediate values. 
  \end{enumerate}
\<close>


definition SP \<comment> \<open>Tag to protect content from further application of arity 
  and combinator equations\<close>
  where [simp]: "SP x \<equiv> x"
lemma SP_cong[cong]: "SP x \<equiv> SP x" by simp
lemma PR_CONST_cong[cong]: "PR_CONST x \<equiv> PR_CONST x" by simp

definition RCALL \<comment> \<open>Tag that marks recursive call\<close>
  where [simp]: "RCALL D \<equiv> D"
definition EVAL \<comment> \<open>Tag that marks evaluation of plain expression for monadify phase\<close>
  where [simp]: "EVAL x \<equiv> RETURN x"

text \<open>
  Internally, the package first applies rewriting rules from 
  \<open>sepref_monadify_arity\<close>, which use eta-expansion to ensure that
  every combinator has enough actual parameters. Moreover, this phase will
  mark recursive calls by the tag @{const RCALL}.

  Next, rewriting rules from \<open>sepref_monadify_comb\<close> are used to
  add @{const EVAL}-tags to plain expressions that should be evaluated
  in the monad. The @{const EVAL} tags are flattened using a default simproc 
  that generates left-to-right argument order.
\<close>

lemma monadify_simps: 
  "Refine_Basic.bind$(RETURN$x)$(\<lambda>\<^sub>2x. f x) = f x" 
  "EVAL$x \<equiv> RETURN$x"
  by simp_all

definition [simp]: "PASS \<equiv> RETURN"
  \<comment> \<open>Pass on value, invalidating old one\<close>

lemma remove_pass_simps:
  "Refine_Basic.bind$(PASS$x)$(\<lambda>\<^sub>2x. f x) \<equiv> f x" 
  "Refine_Basic.bind$m$(\<lambda>\<^sub>2x. PASS$x) \<equiv> m"
  by simp_all


definition COPY :: "'a \<Rightarrow> 'a" 
  \<comment> \<open>Marks required copying of parameter\<close>
  where [simp]: "COPY x \<equiv> x"
lemma RET_COPY_PASS_eq: "RETURN$(COPY$p) = PASS$p" by simp


named_theorems_rev sepref_monadify_arity "Sepref.Monadify: Arity alignment equations"
named_theorems_rev sepref_monadify_comb "Sepref.Monadify: Combinator equations"

ML \<open>
  structure Sepref_Monadify = struct
    local
      fun cr_var (i,T) = ("v"^string_of_int i, Free ("__v"^string_of_int i,T))

      fun lambda2_name n t = let
        val t = @{mk_term "PROTECT2 ?t DUMMY"}
      in
        Term.lambda_name n t
      end


      fun 
        bind_args exp0 [] = exp0
      | bind_args exp0 ((x,m)::xms) = let
          val lr = bind_args exp0 xms 
            |> incr_boundvars 1 
            |> lambda2_name x
        in @{mk_term "Refine_Basic.bind$?m$?lr"} end

      fun monadify t = let
        val (f,args) = Autoref_Tagging.strip_app t
        val _ = not (is_Abs f) orelse 
          raise TERM ("monadify: higher-order",[t])

        val argTs = map fastype_of args
        (*val args = map monadify args*)
        val args = map (fn a => @{mk_term "EVAL$?a"}) args

        (*val fT = fastype_of f
        val argTs = binder_types fT*)
  
        val argVs = tag_list 0 argTs
          |> map cr_var

        val res0 = let
          val x = Autoref_Tagging.list_APP (f,map #2 argVs)
        in 
          @{mk_term "SP (RETURN$?x)"}
        end

        val res = bind_args res0 (argVs ~~ args)
      in
        res
      end

      fun monadify_conv_aux ctxt ct = case Thm.term_of ct of
        @{mpat "EVAL$_"} => let
          val ss = put_simpset HOL_basic_ss ctxt
          val ss = (ss addsimps @{thms monadify_simps SP_def})
          val tac = (simp_tac ss 1)
        in (*Refine_Util.monitor_conv "monadify"*) (
          Refine_Util.f_tac_conv ctxt (dest_comb #> #2 #> monadify) tac) ct
        end
      | t => raise TERM ("monadify_conv",[t])

      (*fun extract_comb_conv ctxt = Conv.rewrs_conv 
        (Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_monadify_evalcomb})
      *)  
    in
      (*
      val monadify_conv = Conv.top_conv 
        (fn ctxt => 
          Conv.try_conv (
            extract_comb_conv ctxt else_conv monadify_conv_aux ctxt
          )
        )
      *)  

      val monadify_simproc = 
        Simplifier.make_simproc @{context} "monadify_simproc"
         {lhss =
          [Logic.varify_global @{term "EVAL$a"}],
          proc = K (try o monadify_conv_aux)};

    end

    local
      open Sepref_Basic
      fun mark_params t = let
        val (P,c,Q,R,a) = dest_hn_refine t
        val pps = strip_star P |> map_filter (dest_hn_ctxt_opt #> map_option #2)

        fun tr env (t as @{mpat "RETURN$?x"}) = 
              if is_Bound x orelse member (aconv) pps x then
                @{mk_term env: "PASS$?x"}
              else t
          | tr env (t1$t2) = tr env t1 $ tr env t2
          | tr env (Abs (x,T,t)) = Abs (x,T,tr (T::env) t)
          | tr _ t = t

        val a = tr [] a
      in
        mk_hn_refine (P,c,Q,R,a)
      end

    in  
    fun mark_params_conv ctxt = Refine_Util.f_tac_conv ctxt 
      (mark_params) 
      (simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms PASS_def}) 1)

    end  

    local

      open Sepref_Basic

      fun dp ctxt (@{mpat "Refine_Basic.bind$(PASS$?p)$(?t' AS\<^sub>p (\<lambda>_. PROTECT2 _ DUMMY))"}) = 
          let
            val (t',ps) = let
                val ((t',rc),ctxt) = dest_lambda_rc ctxt t'
                val f = case t' of @{mpat "PROTECT2 ?f _"} => f | _ => raise Match 
                val (f,ps) = dp ctxt f
                val t' = @{mk_term "PROTECT2 ?f DUMMY"}
                val t' = rc t'
              in
                (t',ps)
              end
  
            val dup = member (aconv) ps p
            val t = if dup then
              @{mk_term "Refine_Basic.bind$(RETURN$(COPY$?p))$?t'"}
            else
              @{mk_term "Refine_Basic.bind$(PASS$?p)$?t'"}
          in
            (t,p::ps)
          end
        | dp ctxt (t1$t2) = (#1 (dp ctxt t1) $ #1 (dp ctxt t2),[])
        | dp ctxt (t as (Abs _)) = (apply_under_lambda (#1 oo dp) ctxt t,[])
        | dp _ t = (t,[])

      fun dp_conv ctxt = Refine_Util.f_tac_conv ctxt 
        (#1 o dp ctxt) 
        (ALLGOALS (simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms RET_COPY_PASS_eq}))) 


    in
      fun dup_tac ctxt = CONVERSION (Sepref_Basic.hn_refine_concl_conv_a dp_conv ctxt)
    end


    fun arity_tac ctxt = let
      val arity1_ss = put_simpset HOL_basic_ss ctxt 
        addsimps ((Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_monadify_arity}))
        |> Simplifier.add_cong @{thm SP_cong}
        |> Simplifier.add_cong @{thm PR_CONST_cong}

      val arity2_ss = put_simpset HOL_basic_ss ctxt 
        addsimps @{thms beta SP_def}
    in
      simp_tac arity1_ss THEN' simp_tac arity2_ss
    end

    fun comb_tac ctxt = let
      val comb1_ss = put_simpset HOL_basic_ss ctxt 
        addsimps (Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_monadify_comb})
        (*addsimps (Named_Theorems_Rev.get ctxt @{named_theorems_rev sepref_monadify_evalcomb})*)
        addsimprocs [monadify_simproc]
        |> Simplifier.add_cong @{thm SP_cong}
        |> Simplifier.add_cong @{thm PR_CONST_cong}

      val comb2_ss = put_simpset HOL_basic_ss ctxt 
        addsimps @{thms SP_def}
    in
      simp_tac comb1_ss THEN' simp_tac comb2_ss
    end

    (*fun ops_tac ctxt = CONVERSION (
      Sepref_Basic.hn_refine_concl_conv_a monadify_conv ctxt)*)

    fun mark_params_tac ctxt = CONVERSION (
      Refine_Util.HOL_concl_conv (K (mark_params_conv ctxt)) ctxt)

    fun contains_eval @{mpat "Trueprop (hn_refine _ _ _ _ ?a)"} =   
      Term.exists_subterm (fn @{mpat EVAL} => true | _ => false) a
    | contains_eval t = raise TERM("contains_eval",[t]);  

    fun remove_pass_tac ctxt = 
      simp_tac (put_simpset HOL_basic_ss ctxt addsimps @{thms remove_pass_simps})

    fun monadify_tac dbg ctxt = let
      open Sepref_Basic
    in
      PHASES' [
        ("arity", arity_tac, 0),
        ("comb", comb_tac, 0),
        (*("ops", ops_tac, 0),*)
        ("check_EVAL", K (CONCL_COND' (not o contains_eval)), 0),
        ("mark_params", mark_params_tac, 0),
        ("dup", dup_tac, 0),
        ("remove_pass", remove_pass_tac, 0)
      ] (flag_phases_ctrl dbg) ctxt
    end

  end
\<close>

lemma dflt_arity[sepref_monadify_arity]:
  "RETURN \<equiv> \<lambda>\<^sub>2x. SP RETURN$x" 
  "RECT \<equiv> \<lambda>\<^sub>2B x. SP RECT$(\<lambda>\<^sub>2D x. B$(\<lambda>\<^sub>2x. RCALL$D$x)$x)$x" 
  "case_list \<equiv> \<lambda>\<^sub>2fn fc l. SP case_list$fn$(\<lambda>\<^sub>2x xs. fc$x$xs)$l" 
  "case_prod \<equiv> \<lambda>\<^sub>2fp p. SP case_prod$(\<lambda>\<^sub>2a b. fp$a$b)$p" 
  "case_option \<equiv> \<lambda>\<^sub>2fn fs ov. SP case_option$fn$(\<lambda>\<^sub>2x. fs$x)$ov" 
  "If \<equiv> \<lambda>\<^sub>2b t e. SP If$b$t$e" 
  "Let \<equiv> \<lambda>\<^sub>2x f. SP Let$x$(\<lambda>\<^sub>2x. f$x)"
  by (simp_all only: SP_def APP_def PROTECT2_def RCALL_def)


lemma dflt_comb[sepref_monadify_comb]:
  "\<And>B x. RECT$B$x \<equiv> Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP (RECT$B$x))"
  "\<And>D x. RCALL$D$x \<equiv> Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP (RCALL$D$x))"
  "\<And>fn fc l. case_list$fn$fc$l \<equiv> Refine_Basic.bind$(EVAL$l)$(\<lambda>\<^sub>2l. (SP case_list$fn$fc$l))"
  "\<And>fp p. case_prod$fp$p \<equiv> Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. (SP case_prod$fp$p))"
  "\<And>fn fs ov. case_option$fn$fs$ov 
    \<equiv> Refine_Basic.bind$(EVAL$ov)$(\<lambda>\<^sub>2ov. (SP case_option$fn$fs$ov))"
  "\<And>b t e. If$b$t$e \<equiv> Refine_Basic.bind$(EVAL$b)$(\<lambda>\<^sub>2b. (SP If$b$t$e))"
  "\<And>x. RETURN$x \<equiv> Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. SP (RETURN$x))"
  "\<And>x f. Let$x$f \<equiv> Refine_Basic.bind$(EVAL$x)$(\<lambda>\<^sub>2x. (SP Let$x$f))"
  by (simp_all)


lemma dflt_plain_comb[sepref_monadify_comb]:
  "EVAL$(If$b$t$e) \<equiv> Refine_Basic.bind$(EVAL$b)$(\<lambda>\<^sub>2b. If$b$(EVAL$t)$(EVAL$e))"
  "EVAL$(case_list$fn$(\<lambda>\<^sub>2x xs. fc x xs)$l) \<equiv> 
    Refine_Basic.bind$(EVAL$l)$(\<lambda>\<^sub>2l. case_list$(EVAL$fn)$(\<lambda>\<^sub>2x xs. EVAL$(fc x xs))$l)"
  "EVAL$(case_prod$(\<lambda>\<^sub>2a b. fp a b)$p) \<equiv> 
    Refine_Basic.bind$(EVAL$p)$(\<lambda>\<^sub>2p. case_prod$(\<lambda>\<^sub>2a b. EVAL$(fp a b))$p)"
  "EVAL$(case_option$fn$(\<lambda>\<^sub>2x. fs x)$ov) \<equiv> 
    Refine_Basic.bind$(EVAL$ov)$(\<lambda>\<^sub>2ov. case_option$(EVAL$fn)$(\<lambda>\<^sub>2x. EVAL$(fs x))$ov)"
  "EVAL $ (Let $ v $ (\<lambda>\<^sub>2x. f x)) \<equiv> (\<bind>) $ (EVAL $ v) $ (\<lambda>\<^sub>2x. EVAL $ (f x))"
  apply (rule eq_reflection, simp split: list.split prod.split option.split)+
  done

lemma evalcomb_PR_CONST[sepref_monadify_comb]:
  "EVAL$(PR_CONST x) \<equiv> SP (RETURN$(PR_CONST x))"
  by simp


end
