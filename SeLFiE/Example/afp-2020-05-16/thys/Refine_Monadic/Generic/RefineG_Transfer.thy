section \<open>Transfer between Domains\<close>
theory RefineG_Transfer
imports "../Refine_Misc"
begin
  text \<open>Currently, this theory is specialized to 
    transfers that include no data refinement.
\<close>


definition "REFINEG_TRANSFER_POST_SIMP x y \<equiv> x=y"
definition [simp]: "REFINEG_TRANSFER_ALIGN x y == True"
lemma REFINEG_TRANSFER_ALIGNI: "REFINEG_TRANSFER_ALIGN x y" by simp

lemma START_REFINEG_TRANSFER: 
  assumes "REFINEG_TRANSFER_ALIGN d c"
  assumes "c\<le>a"
  assumes "REFINEG_TRANSFER_POST_SIMP c d"
  shows "d\<le>a"
  using assms
  by (simp add: REFINEG_TRANSFER_POST_SIMP_def)

lemma STOP_REFINEG_TRANSFER: "REFINEG_TRANSFER_POST_SIMP c c" 
  unfolding REFINEG_TRANSFER_POST_SIMP_def ..

ML \<open>
structure RefineG_Transfer = struct

  structure Post_Processors = Theory_Data (
    type T = (Proof.context -> tactic') Symtab.table
    val empty = Symtab.empty
    val extend = I
    val merge = Symtab.join (K snd)
  )

  fun add_post_processor name tac =
    Post_Processors.map (Symtab.update_new (name,tac))
  fun delete_post_processor name =
    Post_Processors.map (Symtab.delete name)
  val get_post_processors = Post_Processors.get #> Symtab.dest

  fun post_process_tac ctxt = let
    val tacs = get_post_processors (Proof_Context.theory_of ctxt)
      |> map (fn (_,tac) => tac ctxt)

    val tac = REPEAT_DETERM' (CHANGED o EVERY' (map (fn t => TRY o t) tacs))
  in
    tac
  end

  structure Post_Simp = Generic_Data (
      type T = simpset
      val empty = HOL_basic_ss
      val extend = I
      val merge = Raw_Simplifier.merge_ss
  )

  fun post_simps_op f a context = let
    val ctxt = Context.proof_of context
    fun do_it ss = simpset_of (f (put_simpset ss ctxt, a))
  in
    Post_Simp.map do_it context
  end
    
  val add_post_simps = post_simps_op (op addsimps)
  val del_post_simps = post_simps_op (op delsimps)

  fun get_post_ss ctxt = let
    val ss = Post_Simp.get (Context.Proof ctxt)
    val ctxt = put_simpset ss ctxt
  in
    ctxt
  end

  structure post_subst = Named_Thms
    ( val name = @{binding refine_transfer_post_subst}
      val description = "Refinement Framework: " ^ 
        "Transfer postprocessing substitutions" );

  fun post_subst_tac ctxt = let
    val s_thms = post_subst.get ctxt
    val dis_tac = (ALLGOALS (Tagged_Solver.solve_tac ctxt))
    val cnv = Cond_Rewr_Conv.cond_rewrs_conv dis_tac s_thms
    val ts_conv = Conv.top_sweep_conv cnv ctxt
    val ss = get_post_ss ctxt
  in
    REPEAT o CHANGED o 
    (Simplifier.simp_tac ss THEN' CONVERSION ts_conv)
  end


  structure transfer = Named_Thms
    ( val name = @{binding refine_transfer}
      val description = "Refinement Framework: " ^ 
        "Transfer rules" );

  fun transfer_tac thms ctxt i st = let 
    val thms = thms @ transfer.get ctxt;
    val ss = put_simpset HOL_basic_ss ctxt addsimps @{thms nested_case_prod_simp}
  in
    REPEAT_DETERM1 (
      COND (has_fewer_prems (Thm.nprems_of st)) no_tac (
        FIRST [
          Method.assm_tac ctxt i,
          resolve_tac ctxt thms i,
          Tagged_Solver.solve_tac ctxt i,
          CHANGED_PROP (simp_tac ss i)]
      )) st
  end

  (* Adjust right term to have same structure as left one *)
  fun align_tac ctxt = IF_EXGOAL (fn i => fn st =>
    case Logic.concl_of_goal (Thm.prop_of st) i of
      @{mpat "Trueprop (REFINEG_TRANSFER_ALIGN ?c _)"} => let
        val c = Thm.cterm_of ctxt c
        val cT = Thm.ctyp_of_cterm c
        
        val rl = @{thm REFINEG_TRANSFER_ALIGNI}
          |> Thm.incr_indexes (Thm.maxidx_of st + 1)
          |> Thm.instantiate' [NONE,SOME cT] [NONE,SOME c]
        (*val _ = tracing (@{make_string} rl)*)
      in
        resolve_tac ctxt [rl] i st
      end
    | _ => Seq.empty
  )

  fun post_transfer_tac thms ctxt = let open Autoref_Tacticals in
    resolve_tac ctxt @{thms START_REFINEG_TRANSFER} 
    THEN' align_tac ctxt 
    THEN' IF_SOLVED (transfer_tac thms ctxt)
      (post_process_tac ctxt THEN' resolve_tac ctxt @{thms STOP_REFINEG_TRANSFER})
      (K all_tac)

  end

  fun get_post_simp_rules context = Context.proof_of context
      |> get_post_ss
      |> simpset_of 
      |> Raw_Simplifier.dest_ss
      |> #simps |> map snd


  local
    val add_ps = Thm.declaration_attribute (add_post_simps o single)
    val del_ps = Thm.declaration_attribute (del_post_simps o single)
  in
    val setup = I
      #> add_post_processor "RefineG_Transfer.post_subst" post_subst_tac
      #> post_subst.setup
      #> transfer.setup
      #> Attrib.setup @{binding refine_transfer_post_simp} 
          (Attrib.add_del add_ps del_ps) 
          ("declaration of transfer post simplification rules")
      #> Global_Theory.add_thms_dynamic (
           @{binding refine_transfer_post_simps}, get_post_simp_rules)

  end
end
\<close>

setup \<open>RefineG_Transfer.setup\<close>
method_setup refine_transfer = 
  \<open>Scan.lift (Args.mode "post") -- Attrib.thms 
  >> (fn (post,thms) => fn ctxt => SIMPLE_METHOD'
    ( if post then RefineG_Transfer.post_transfer_tac thms ctxt
      else RefineG_Transfer.transfer_tac thms ctxt))
\<close> "Invoke transfer rules"


locale transfer = fixes \<alpha> :: "'c \<Rightarrow> 'a::complete_lattice"
begin

text \<open>
  In the following, we define some transfer lemmas for general
  HOL - constructs.
\<close>

lemma transfer_if[refine_transfer]:
  assumes "b \<Longrightarrow> \<alpha> s1 \<le> S1"
  assumes "\<not>b \<Longrightarrow> \<alpha> s2 \<le> S2"
  shows "\<alpha> (if b then s1 else s2) \<le> (if b then S1 else S2)"
  using assms by auto

lemma transfer_prod[refine_transfer]:
  assumes "\<And>a b. \<alpha> (f a b) \<le> F a b"
  shows "\<alpha> (case_prod f x) \<le> (case_prod F x)"
  using assms by (auto split: prod.split)

lemma transfer_Let[refine_transfer]:
  assumes "\<And>x. \<alpha> (f x) \<le> F x"
  shows "\<alpha> (Let x f) \<le> Let x F"
  using assms by auto

lemma transfer_option[refine_transfer]:
  assumes "\<alpha> fa \<le> Fa"
  assumes "\<And>x. \<alpha> (fb x) \<le> Fb x"
  shows "\<alpha> (case_option fa fb x) \<le> case_option Fa Fb x"
  using assms by (auto split: option.split)

lemma transfer_sum[refine_transfer]:
  assumes "\<And>l. \<alpha> (fl l) \<le> Fl l"
  assumes "\<And>r. \<alpha> (fr r) \<le> Fr r"
  shows "\<alpha> (case_sum fl fr x) \<le> (case_sum Fl Fr x)"
  using assms by (auto split: sum.split)

lemma transfer_list[refine_transfer]:
  assumes "\<alpha> fn \<le> Fn"
  assumes "\<And>x xs. \<alpha> (fc x xs) \<le> Fc x xs"
  shows "\<alpha> (case_list fn fc l) \<le> case_list Fn Fc l"
  using assms by (auto split: list.split)


lemma transfer_rec_list[refine_transfer]:
  assumes FN: "\<And>s. \<alpha> (fn s) \<le> fn' s"
  assumes FC: "\<And>x l rec rec' s. \<lbrakk> \<And>s. \<alpha> (rec s) \<le> (rec' s) \<rbrakk> 
    \<Longrightarrow> \<alpha> (fc x l rec s) \<le> fc' x l rec' s"
  shows "\<alpha> (rec_list fn fc l s) \<le> rec_list fn' fc' l s"
  apply (induct l arbitrary: s)
  apply (simp add: FN)
  apply (simp add: FC)
  done

lemma transfer_rec_nat[refine_transfer]:
  assumes FN: "\<And>s. \<alpha> (fn s) \<le> fn' s"
  assumes FC: "\<And>n rec rec' s. \<lbrakk> \<And>s. \<alpha> (rec s) \<le> rec' s \<rbrakk> 
    \<Longrightarrow> \<alpha> (fs n rec s) \<le> fs' n rec' s"
  shows "\<alpha> (rec_nat fn fs n s) \<le> rec_nat fn' fs' n s"
  apply (induct n arbitrary: s)
  apply (simp add: FN)
  apply (simp add: FC)
  done

end

text \<open>Transfer into complete lattice structure\<close>
locale ordered_transfer = transfer + 
  constrains \<alpha> :: "'c::complete_lattice \<Rightarrow> 'a::complete_lattice"

text \<open>Transfer into complete lattice structure with distributive
  transfer function.\<close>
locale dist_transfer = ordered_transfer + 
  constrains \<alpha> :: "'c::complete_lattice \<Rightarrow> 'a::complete_lattice"
  assumes \<alpha>_dist: "\<And>A. is_chain A \<Longrightarrow> \<alpha> (Sup A) = Sup (\<alpha>`A)"
begin
  lemma \<alpha>_mono[simp, intro!]: "mono \<alpha>"
    apply rule
    apply (subgoal_tac "is_chain {x,y}")
    apply (drule \<alpha>_dist)
    apply (auto simp: le_iff_sup) []
    apply (rule chainI)
    apply auto
    done

  lemma \<alpha>_strict[simp]: "\<alpha> bot = bot"
    using \<alpha>_dist[of "{}"] by simp
end


text \<open>Transfer into ccpo\<close>
locale ccpo_transfer = transfer \<alpha> for
  \<alpha> :: "'c::ccpo \<Rightarrow> 'a::complete_lattice" 

text \<open>Transfer into ccpo with distributive
  transfer function.\<close>
locale dist_ccpo_transfer = ccpo_transfer \<alpha>
  for \<alpha> :: "'c::ccpo \<Rightarrow> 'a::complete_lattice" + 
  assumes \<alpha>_dist: "\<And>A. is_chain A \<Longrightarrow> \<alpha> (Sup A) = Sup (\<alpha>`A)"
begin

  lemma \<alpha>_mono[simp, intro!]: "mono \<alpha>"
  proof
    fix x y :: 'c
    assume LE: "x\<le>y"
    hence C[simp, intro!]: "is_chain {x,y}" by (auto intro: chainI)
    from LE have "\<alpha> x \<le> sup (\<alpha> x) (\<alpha> y)" by simp
    also have "\<dots> = Sup (\<alpha>`{x,y})" by simp
    also have "\<dots> = \<alpha> (Sup {x,y})"
      by (rule \<alpha>_dist[symmetric]) simp
    also have "Sup {x,y} = y"
      apply (rule antisym)
      apply (rule ccpo_Sup_least[OF C]) using LE apply auto []
      apply (rule ccpo_Sup_upper[OF C]) by auto
    finally show "\<alpha> x \<le> \<alpha> y" .
  qed

  lemma \<alpha>_strict[simp]: "\<alpha> (Sup {}) = bot"
    using \<alpha>_dist[of "{}"] by simp
end

end
