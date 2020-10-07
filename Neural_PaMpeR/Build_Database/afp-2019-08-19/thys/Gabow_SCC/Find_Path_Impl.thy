section \<open>Implementation of Safety Property Model Checker \label{sec:find_path_impl}\<close>
theory Find_Path_Impl
imports 
  Find_Path
  CAVA_Automata.Digraph_Impl
begin

  section \<open>Workset Algorithm\<close>
  text \<open>A simple implementation is by a workset algorithm.\<close>
  definition "ws_update E u p V ws \<equiv> RETURN (
             V \<union> E``{u}, 
             ws ++ (\<lambda>v. if (u,v)\<in>E \<and> v\<notin>V then Some (u#p) else None))"

  definition "s_init U0 \<equiv> RETURN (None,U0,\<lambda>u. if u\<in>U0 then Some [] else None)"

  definition "wset_find_path E U0 P \<equiv> do {
    ASSERT (finite U0);
    s0 \<leftarrow> s_init U0;
    (res,_,_) \<leftarrow> WHILET 
      (\<lambda>(res,V,ws). res=None \<and> ws\<noteq>Map.empty)
      (\<lambda>(res,V,ws). do {
        ASSERT (ws\<noteq>Map.empty);
        (u,p) \<leftarrow> SPEC (\<lambda>(u,p). ws u = Some p);
        let ws=ws |` (-{u});
        
        if P u then
          RETURN (Some (rev p,u),V,ws)
        else do {
          ASSERT (finite (E``{u}));
          ASSERT (dom ws \<subseteq> V);
          (V,ws) \<leftarrow> ws_update E u p V ws;
          RETURN (None,V,ws)
        }
      }) s0;
      RETURN res
    }"

  lemma wset_find_path_correct:
    fixes E :: "('v\<times>'v) set"
    shows "wset_find_path E U0 P \<le> find_path E U0 P"
  proof -

    define inv where "inv = (\<lambda>(res,V,ws). case res of
        None \<Rightarrow> 
          dom ws\<subseteq>V 
        \<and> finite (dom ws)  \<comment> \<open>Derived\<close>
        \<and> V\<subseteq>E\<^sup>*``U0 
        \<and> E``(V-dom ws) \<subseteq> V 
        \<and> (\<forall>v\<in>V-dom ws. \<not> P v)
        \<and> U0 \<subseteq> V
        \<and> (\<forall>v p. ws v = Some p 
          \<longrightarrow> ((\<forall>v\<in>set p. \<not>P v) \<and> (\<exists>u0\<in>U0. path E u0 (rev p) v)))
      | Some (p,v) \<Rightarrow> (\<exists>u0\<in>U0. path E u0 p v \<and> P v \<and> (\<forall>v\<in>set p. \<not>P v)))"

    define var where "var = inv_image 
        (brk_rel (finite_psupset (E\<^sup>*``U0) <*lex*> measure (card o dom)))
        (\<lambda>(res::('v list \<times> 'v) option,V::'v set,ws::'v\<rightharpoonup>'v list). 
            (res\<noteq>None,V,ws))"

    (*have [simp, intro!]: "wf var"
      unfolding var_def
      by (auto intro: FIN)*)

    have [simp]: "\<And>u p V. dom (\<lambda>v. if (u, v) \<in> E \<and> v \<notin> V then Some (u # p)
                     else None) = E``{u} - V"
      by (auto split: if_split_asm)


    {
      fix V ws u p
      assume INV: "inv (None,V,ws)"
      assume WSU: "ws u = Some p"

      from INV WSU have 
        [simp]: "V \<subseteq> E\<^sup>*``U0"
        and [simp]: "u \<in> V"
        and UREACH: "\<exists>u0\<in>U0. (u0,u)\<in>E\<^sup>*"
        and [simp]: "finite (dom ws)"
        unfolding inv_def
        apply simp_all
        apply auto []
        apply clarsimp
        apply blast
        done
      have "(V \<union> E `` {u}, V) \<in> finite_psupset (E\<^sup>* `` U0) \<or>
          V \<union> E `` {u} = V \<and>
          card (E `` {u} - V \<union> (dom ws - {u})) < card (dom ws)"
      proof (subst disj_commute, intro disjCI conjI)
        assume "(V \<union> E `` {u}, V) \<notin> finite_psupset (E\<^sup>* `` U0)"
        thus "V \<union> E `` {u} = V" using UREACH 
          by (auto simp: finite_psupset_def intro: rev_ImageI)

        hence [simp]: "E``{u} - V = {}" by force
        show "card (E `` {u} - V \<union> (dom ws - {u})) < card (dom ws)"
          using WSU
          by (auto intro: card_Diff1_less)
      qed
    } note wf_aux=this

    {
      fix V ws u p
      assume FIN: "finite (E\<^sup>*``U0)"
      assume "inv (None,V,ws)" "ws u = Some p"
      then obtain u0 where "u0\<in>U0" "(u0,u)\<in>E\<^sup>*" unfolding inv_def 
        by clarsimp blast
      hence "E``{u} \<subseteq> E\<^sup>*``U0" by (auto intro: rev_ImageI)
      hence "finite (E``{u})" using FIN(1) by (rule finite_subset)
    } note succs_finite=this

    {
      fix V ws u p
      assume FIN: "finite (E\<^sup>*``U0)"
      assume INV: "inv (None,V,ws)"
      assume WSU: "ws u = Some p"
      assume NVD: "\<not> P u"

      have "inv (None, V \<union> E `` {u},
               ws |` (- {u}) ++
               (\<lambda>v. if (u, v) \<in> E \<and> v \<notin> V then Some (u # p)
                    else None))" 
        unfolding inv_def
        
        apply (simp, intro conjI)
        using INV WSU apply (auto simp: inv_def) []
        using INV WSU apply (auto simp: inv_def) []
        using INV WSU apply (auto simp: succs_finite FIN) []
        using INV apply (auto simp: inv_def) []
        using INV apply (auto simp: inv_def) []

        using INV WSU apply (auto 
          simp: inv_def 
          intro: rtrancl_image_advance
        ) []

        using INV WSU apply (auto simp: inv_def) []

        using INV NVD apply (auto simp: inv_def) []
        using INV NVD apply (auto simp: inv_def) []

        using INV WSU NVD apply (fastforce
          simp: inv_def restrict_map_def 
          intro!: path_conc path1
          split: if_split_asm
        ) []
        done
    } note ip_aux=this

    show ?thesis
      unfolding wset_find_path_def find_path_def ws_update_def s_init_def

      apply (refine_rcg refine_vcg le_ASSERTI
        WHILET_rule[where 
          R = var and I = inv]
      )
      
      using [[goals_limit = 1]]

      apply (auto simp: var_def) []

      apply (auto 
        simp: inv_def dom_def
        split: if_split_asm) []
      apply simp
      apply (auto simp: inv_def) []
      apply (auto simp: var_def brk_rel_def) []

      apply (simp add: succs_finite)

      apply (auto simp: inv_def) []

      apply clarsimp
      apply (simp add: ip_aux)

      apply clarsimp
      apply (simp add: var_def brk_rel_def wf_aux) []

      apply (fastforce
        simp: inv_def 
        split: option.splits 
        intro: rev_ImageI
        dest: Image_closed_trancl) []
      done
  qed

  text \<open>We refine the algorithm to use a foreach-loop\<close>
  definition "ws_update_foreach E u p V ws \<equiv> 
    FOREACH (LIST_SET_REV_TAG (E``{u})) (\<lambda>v (V,ws). 
      if v\<in>V then 
        RETURN (V,ws) 
      else do {
        ASSERT (v\<notin>dom ws);
        RETURN (insert v V,ws( v \<mapsto> u#p))
      }
    ) (V,ws)"

  lemma ws_update_foreach_refine[refine]:
    assumes FIN: "finite (E``{u})"
    assumes WSS: "dom ws \<subseteq> V"
    assumes ID: "(E',E)\<in>Id" "(u',u)\<in>Id" "(p',p)\<in>Id" "(V',V)\<in>Id" "(ws',ws)\<in>Id"
    shows "ws_update_foreach E' u' p' V' ws' \<le> \<Down>Id (ws_update E u p V ws)"
    unfolding ID[simplified]
    unfolding ws_update_foreach_def ws_update_def LIST_SET_REV_TAG_def
    apply (refine_rcg refine_vcg FIN
      FOREACH_rule[where I="\<lambda>it (V',ws'). 
        V'=V \<union> (E``{u}-it)
      \<and> dom ws' \<subseteq> V'
      \<and> ws' = ws ++ (\<lambda>v. if (u,v)\<in>E \<and> v\<notin>it \<and> v\<notin>V then Some (u#p) else None)"]
    )
    using WSS
    apply (auto 
      simp: Map.map_add_def
      split: option.splits if_split_asm
      intro!: ext[where 'a='a and 'b="'b list option"])

    apply fastforce+
    done

  definition "s_init_foreach U0 \<equiv> do {
      (U0,ws) \<leftarrow> FOREACH U0 (\<lambda>x (U0,ws). 
        RETURN (insert x U0,ws(x\<mapsto>[]))) ({},Map.empty);
      RETURN (None,U0,ws)
    }"

  lemma s_init_foreach_refine[refine]:
    assumes FIN: "finite U0"
    assumes ID: "(U0',U0)\<in>Id"
    shows "s_init_foreach U0' \<le>\<Down>Id (s_init U0)"
    unfolding s_init_foreach_def s_init_def ID[simplified]
    
    apply (refine_rcg refine_vcg
      FOREACH_rule[where 
        I = "\<lambda>it (U,ws). 
          U = U0-it 
        \<and> ws = (\<lambda>x. if x\<in>U0-it then Some [] else None)"]
    )

    apply (auto
      simp: FIN
      intro!: ext
    )
    done

  definition "wset_find_path' E U0 P \<equiv> do {
    ASSERT (finite U0);
    s0\<leftarrow>s_init_foreach U0;
    (res,_,_) \<leftarrow> WHILET 
      (\<lambda>(res,V,ws). res=None \<and> ws\<noteq>Map.empty)
      (\<lambda>(res,V,ws). do {
        ASSERT (ws\<noteq>Map.empty);
        ((u,p),ws) \<leftarrow> op_map_pick_remove ws;
        
        if P u then
          RETURN (Some (rev p,u),V,ws)
        else do {
          (V,ws) \<leftarrow> ws_update_foreach E u p V ws;
          RETURN (None,V,ws)
        }
      })
      s0;
      RETURN res
    }"

  lemma wset_find_path'_refine: 
    "wset_find_path' E U0 P \<le> \<Down>Id (wset_find_path E U0 P)"
    unfolding wset_find_path'_def wset_find_path_def
    unfolding op_map_pick_remove_alt
    apply (refine_rcg IdI)
    apply assumption
    apply simp_all
    done

  section \<open>Refinement to efficient data structures\<close>
  schematic_goal wset_find_path'_refine_aux:
    fixes U0::"'a::hashable set" and P::"'a \<Rightarrow> bool" and E::"('a\<times>'a) set"
    assumes [autoref_rules]: 
      "(succi,E)\<in>\<langle>Id\<rangle>slg_rel"
      "(U0',U0)\<in>\<langle>Id\<rangle>list_set_rel"
    notes [autoref_tyrel] = 
      TYRELI[where 
        R="\<langle>Id::(('a\<times>'a) set),\<langle>Id::(('a\<times>'a) set)\<rangle>list_rel\<rangle>list_map_rel"]
      TYRELI[where R="\<langle>Id::(('a\<times>'a) set)\<rangle>map2set_rel dflt_ahm_rel"]

    notes [autoref_rules] = 
      IdI[of P, unfolded fun_rel_id_simp[symmetric]]

    shows "(?c::?'c,wset_find_path' E U0 P) \<in> ?R"
    unfolding wset_find_path'_def ws_update_foreach_def s_init_foreach_def
    using [[autoref_trace_failed_id]]
    using [[autoref_trace_intf_unif]]
    using [[autoref_trace_pat]]
    apply (autoref (keep_goal))
    done

  concrete_definition wset_find_path_impl for succi U0' P 
    uses wset_find_path'_refine_aux

  section \<open>Autoref Setup\<close>
  context begin interpretation autoref_syn .
    lemma [autoref_itype]: 
      "find_path ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i (I\<rightarrow>\<^sub>ii_bool) 
        \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_list, I\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option\<rangle>\<^sub>ii_nres" by simp

    lemma wset_find_path_autoref[autoref_rules]:
      shows "(
        wset_find_path_impl, 
        find_path)
        \<in> \<langle>Id\<rangle>slg_rel \<rightarrow> \<langle>Id\<rangle>list_set_rel \<rightarrow> (Id\<rightarrow>bool_rel) 
          \<rightarrow> \<langle>\<langle>\<langle>Id\<rangle>list_rel\<times>\<^sub>rId\<rangle>option_rel\<rangle>nres_rel"
    proof -
      note wset_find_path_impl.refine[THEN nres_relD]
      also note wset_find_path'_refine
      also note wset_find_path_correct
      finally show ?thesis 
        by (fastforce intro!: nres_relI)
    qed
  end
    
  schematic_goal wset_find_path_transfer_aux: 
    "RETURN ?c \<le> wset_find_path_impl E U0 P"
    unfolding wset_find_path_impl_def
    by (refine_transfer (post))
  concrete_definition wset_find_path_code 
    for E ?U0.0 P uses wset_find_path_transfer_aux
  lemmas [refine_transfer] = wset_find_path_code.refine

  export_code wset_find_path_code checking SML

section \<open>Nontrivial paths\<close>

definition "find_path1_gen E u0 P \<equiv> do {
  res \<leftarrow> find_path E (E``{u0}) P;
  case res of None \<Rightarrow> RETURN None
    | Some (p,v) \<Rightarrow> RETURN (Some (u0#p,v))
  }"

lemma find_path1_gen_correct: "find_path1_gen E u0 P \<le> find_path1 E u0 P"
  unfolding find_path1_gen_def find_path_def find_path1_def
  apply (refine_rcg refine_vcg le_ASSERTI)
  apply (auto 
    intro: path_prepend 
    dest: tranclD
    elim: finite_subset[rotated]
  )
  done

schematic_goal find_path1_impl_aux:
  shows "(?c::?'c,find_path1_gen::(_\<times>_::hashable) set \<Rightarrow> _)\<in>?R"
  unfolding find_path1_gen_def[abs_def]
  apply (autoref (keep_goal))
  done

lemma [autoref_itype]: 
  "find_path1 ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i (I\<rightarrow>\<^sub>ii_bool) 
    \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>\<langle>I\<rangle>\<^sub>ii_list, I\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_option\<rangle>\<^sub>ii_nres" by simp

concrete_definition find_path1_impl uses find_path1_impl_aux

lemma find_path1_autoref[autoref_rules]: 
  "(find_path1_impl,find_path1) 
    \<in> \<langle>Id\<rangle>slg_rel \<rightarrow>Id \<rightarrow> (Id \<rightarrow> bool_rel) \<rightarrow> 
      \<langle>\<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>Relators.option_rel\<rangle>nres_rel"
  apply (rule fun_relI nres_relI)+
  apply (rule order_trans)
  apply (erule (2) find_path1_impl.refine[param_fo, THEN nres_relD])
  apply (simp add: find_path1_gen_correct)
  done
  
schematic_goal find_path1_transfer_aux: 
  "RETURN ?c \<le> find_path1_impl E u P"
  unfolding find_path1_impl_def
  by refine_transfer
concrete_definition find_path1_code for E u P uses find_path1_transfer_aux
lemmas [refine_transfer] = find_path1_code.refine

end
