section \<open>Implementing Graphs by Maps\<close>
theory GraphByMap
imports 
  GraphSpec 
  GraphGA
begin

definition "map_Sigma M1 F2 \<equiv> {
  (x,y). \<exists>v. M1 x = Some v \<and> y\<in>F2 v
}"

lemma map_Sigma_alt: "map_Sigma M1 F2 = Sigma (dom M1) (\<lambda>x.
  F2 (the (M1 x)))"
  unfolding map_Sigma_def
  by auto
  
(* TODO: Move to Misc *)
lemma ranE: 
  assumes "v\<in>ran m"
  obtains k where "m k = Some v"
  using assms
by (metis ran_restrictD restrict_map_self)
lemma option_bind_alt:
  "Option.bind x f = (case x of None \<Rightarrow> None | Some v \<Rightarrow> f v)"
  by (auto split: option.split)

locale GraphByMapDefs = 
  m1: StdMapDefs m1_ops +
  m2: StdMapDefs m2_ops +
  s3: StdSetDefs s3_ops
  for m1_ops::"('V,'m2,'m1,_) map_ops_scheme"
  and m2_ops::"('V,'s3,'m2,_) map_ops_scheme"
  and s3_ops::"('W,'s3,_) set_ops_scheme"
  and m1_mvif :: "('V \<Rightarrow> 'm2 \<rightharpoonup> 'm2) \<Rightarrow> 'm1 \<Rightarrow> 'm1"
begin
  definition gbm_\<alpha> :: "('V,'W,'m1) graph_\<alpha>" where
    "gbm_\<alpha> m1 \<equiv>
    \<lparr> nodes = dom (m1.\<alpha> m1),
      edges = {(v,w,v'). 
        \<exists>m2 s3. m1.\<alpha> m1 v = Some m2 
          \<and> m2.\<alpha> m2 v' = Some s3
          \<and> w\<in>s3.\<alpha> s3
      }
    \<rparr>"

  definition "gbm_invar m1 \<equiv>
    m1.invar m1 \<and>
    (\<forall>m2\<in>ran (m1.\<alpha> m1). m2.invar m2 \<and>
      (\<forall>s3\<in>ran (m2.\<alpha> m2). s3.invar s3)
    ) \<and> valid_graph (gbm_\<alpha> m1)"

  definition gbm_empty :: "('V,'W,'m1) graph_empty" where 
    "gbm_empty \<equiv> m1.empty"

  definition gbm_add_node :: "('V,'W,'m1) graph_add_node" where
    "gbm_add_node v g \<equiv> case m1.lookup v g of
    None \<Rightarrow> m1.update v (m2.empty ()) g |
    Some _ \<Rightarrow> g"

  definition gbm_delete_node :: "('V,'W,'m1) graph_delete_node" where
    "gbm_delete_node v g \<equiv> let g=m1.delete v g in
    m1_mvif (\<lambda>_ m2. Some (m2.delete v m2)) g"

  definition gbm_add_edge :: "('V,'W,'m1) graph_add_edge" where
    "gbm_add_edge v e v' g \<equiv> 
    let g = (case m1.lookup v' g of 
      None \<Rightarrow> m1.update v' (m2.empty ()) g | Some _ \<Rightarrow> g
    ) in
    case m1.lookup v g of 
      None \<Rightarrow> (m1.update v (m2.sng v' (s3.sng e)) g) |
      Some m2 \<Rightarrow> (case m2.lookup v' m2 of
        None \<Rightarrow> m1.update v (m2.update v' (s3.sng e) m2) g |
        Some s3 \<Rightarrow> m1.update v (m2.update v' (s3.ins e s3) m2) g)
    "

  definition gbm_delete_edge :: "('V,'W,'m1) graph_delete_edge" where
    "gbm_delete_edge v e v' g \<equiv>
    case m1.lookup v g of
      None \<Rightarrow> g |
      Some m2 \<Rightarrow> (
        case m2.lookup v' m2 of
          None \<Rightarrow> g |
          Some s3 \<Rightarrow> m1.update v (m2.update v' (s3.delete e s3) m2) g
      )
    "

  definition gbm_nodes_list_it 
    :: "('V,'W,'V list,'m1) graph_nodes_it"
    where
    "gbm_nodes_list_it g \<equiv> map_iterator_dom (m1.iteratei g)"
  local_setup \<open>Locale_Code.lc_decl_del @{term gbm_nodes_list_it}\<close>

  definition gbm_edges_list_it 
    :: "('V,'W,('V\<times>'W\<times>'V) list,'m1) graph_edges_it"
    where
    "gbm_edges_list_it g \<equiv> set_iterator_image 
      (\<lambda>((v1,m1),(v2,m2),w). (v1,w,v2)) 
      (set_iterator_product (m1.iteratei g) 
        (\<lambda>(v,m2). set_iterator_product 
          (m2.iteratei m2) (\<lambda>(w,s3). s3.iteratei s3)))
    "
  local_setup \<open>Locale_Code.lc_decl_del @{term gbm_edges_list_it}\<close>

  definition gbm_succ_list_it ::
    "('V,'W,('W\<times>'V) list,'m1) graph_succ_it"
    where
  "gbm_succ_list_it g v \<equiv> case m1.lookup v g of
    None \<Rightarrow> set_iterator_emp |
    Some m2 \<Rightarrow> 
      set_iterator_image (\<lambda>((v',m2),w). (w,v')) 
        (set_iterator_product (m2.iteratei m2) (\<lambda>(v',s). s3.iteratei s))
    "
  local_setup \<open>Locale_Code.lc_decl_del @{term gbm_succ_list_it}\<close>

  definition 
    "gbm_from_list \<equiv> gga_from_list gbm_empty gbm_add_node gbm_add_edge"


  lemma gbm_nodes_list_it_unf:
    "it_to_it (gbm_nodes_list_it g) 
    \<equiv> map_iterator_dom (it_to_it (m1.list_it g))"
    apply (rule eq_reflection)
    apply (rule it_to_it_fold)
    unfolding gbm_nodes_list_it_def m1.iteratei_def
    by (intro icf_proper_iteratorI)

  lemma gbm_edges_list_it_unf:
    "it_to_it (gbm_edges_list_it g) 
    \<equiv> set_iterator_image 
      (\<lambda>((v1,m1),(v2,m2),w). (v1,w,v2)) 
      (set_iterator_product (it_to_it (m1.list_it g)) 
        (\<lambda>(v,m2). set_iterator_product 
          (it_to_it (m2.list_it m2)) (\<lambda>(w,s3). (it_to_it (s3.list_it s3)))))
    "
    apply (rule eq_reflection)
    apply (rule it_to_it_fold)
    unfolding gbm_edges_list_it_def 
      m1.iteratei_def m2.iteratei_def s3.iteratei_def
    apply (intro icf_proper_iteratorI allI impI, (simp split: prod.split)?)+
    done

  lemma gbm_succ_list_it_unf:
  "it_to_it (gbm_succ_list_it g v) \<equiv> 
    case m1.lookup v g of
      None \<Rightarrow> set_iterator_emp |
      Some m2 \<Rightarrow> 
        set_iterator_image (\<lambda>((v',m2),w). (w,v')) 
          (set_iterator_product (it_to_it (m2.list_it m2)) 
            (\<lambda>(v',s). (it_to_it (s3.list_it s))))
      "
    apply (rule eq_reflection)
    apply (rule it_to_it_fold)
    unfolding gbm_succ_list_it_def 
      m2.iteratei_def s3.iteratei_def
    apply (simp split: prod.split option.split)
    apply (intro icf_proper_iteratorI allI impI conjI, 
      (simp split: prod.split option.split)?)+
    done


end

sublocale GraphByMapDefs < graph_nodes_it_defs gbm_nodes_list_it .
sublocale GraphByMapDefs < graph_edges_it_defs gbm_edges_list_it .
sublocale GraphByMapDefs < graph_succ_it_defs gbm_succ_list_it .
sublocale GraphByMapDefs 
  < gga_to_list_defs_loc gbm_nodes_list_it gbm_edges_list_it .

context GraphByMapDefs
begin

  definition [icf_rec_def]: "gbm_ops \<equiv> \<lparr>
    gop_\<alpha> = gbm_\<alpha>,
    gop_invar = gbm_invar,
    gop_empty = gbm_empty,
    gop_add_node = gbm_add_node,
    gop_delete_node = gbm_delete_node,
    gop_add_edge = gbm_add_edge,
    gop_delete_edge = gbm_delete_edge,
    gop_from_list = gbm_from_list,
    gop_to_list = gga_to_list,
    gop_nodes_list_it = gbm_nodes_list_it,
    gop_edges_list_it = gbm_edges_list_it,
    gop_succ_list_it  = gbm_succ_list_it
    \<rparr>"
  local_setup \<open>Locale_Code.lc_decl_del @{term gbm_ops}\<close>
end

locale GraphByMap = GraphByMapDefs m1_ops m2_ops s3_ops m1_mvif +
  m1: StdMap m1_ops +
  m2: StdMap m2_ops +
  s3: StdSet s3_ops +
  m1: map_value_image_filter m1.\<alpha> m1.invar m1.\<alpha> m1.invar m1_mvif
  for m1_ops::"('V,'m2,'m1,_) map_ops_scheme"
  and m2_ops::"('V,'s3,'m2,_) map_ops_scheme"
  and s3_ops::"('W,'s3,_) set_ops_scheme"
  and m1_mvif :: "('V \<Rightarrow> 'm2 \<rightharpoonup> 'm2) \<Rightarrow> 'm1 \<Rightarrow> 'm1"
begin
  lemma gbm_invar_split: 
    assumes "gbm_invar g"
    shows
    "m1.invar g"
    "\<And>v m2. m1.\<alpha> g v = Some m2 \<Longrightarrow> m2.invar m2"
    "\<And>v m2 v' s3. m1.\<alpha> g v = Some m2 \<Longrightarrow> m2.\<alpha> m2 v' = Some s3 \<Longrightarrow> s3.invar s3"
    "valid_graph (gbm_\<alpha> g)"
    using assms unfolding gbm_invar_def 
    by (auto intro: ranI)

end

sublocale GraphByMap < graph gbm_\<alpha> gbm_invar
proof
  fix g
  assume INV: "gbm_invar g"
  then interpret vg: valid_graph "(gbm_\<alpha> g)" by (simp add: gbm_invar_def)
  
  from vg.E_valid
  show "fst ` edges (gbm_\<alpha> g) \<subseteq> nodes (gbm_\<alpha> g)" and
    "snd ` snd ` edges (gbm_\<alpha> g) \<subseteq> nodes (gbm_\<alpha> g)" .

  from INV show "finite (nodes (gbm_\<alpha> g))"
    unfolding gbm_invar_def gbm_\<alpha>_def by auto

  note [simp] = gbm_invar_split[OF INV]

  show "finite (edges (gbm_\<alpha> g))"
    apply (rule finite_imageD[where f="\<lambda>(v,e,v'). (v,v',e)"])
    apply (rule finite_subset[where B=
      "map_Sigma (m1.\<alpha> g) (\<lambda>m2. map_Sigma (m2.\<alpha> m2) (s3.\<alpha>))"])
    apply (auto simp add: map_Sigma_def gbm_\<alpha>_def) []
    apply (unfold map_Sigma_alt)
    apply (auto intro!: finite_SigmaI inj_onI)
    done
qed

context GraphByMap
begin

  lemma gbm_empty_impl: 
    "graph_empty gbm_\<alpha> gbm_invar gbm_empty"
    apply (unfold_locales)
    unfolding gbm_\<alpha>_def gbm_invar_def gbm_empty_def
    apply (auto simp: m1.correct Graph.empty_def)
    apply (unfold_locales)
    apply auto
    done

  lemma gbm_add_node_impl:
    "graph_add_node gbm_\<alpha> gbm_invar gbm_add_node"
  proof
    fix g v
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_add_node v g) = add_node v (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_add_node_def
      by (auto simp: m1.correct m2.correct s3.correct add_node_def
        split: option.split if_split_asm)
    
    thus "gbm_invar (gbm_add_node v g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_add_node_def add_node_def 
      apply (auto simp: m1.correct m2.correct s3.correct add_node_def
        split: option.split if_split_asm elim!: ranE)
      done
  qed

  lemma gbm_delete_node_impl:
    "graph_delete_node gbm_\<alpha> gbm_invar gbm_delete_node"
  proof
    fix g v
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_delete_node v g) = delete_node v (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_delete_node_def
      by (auto simp: restrict_map_def option_bind_alt
        m1.correct m2.correct s3.correct m1.map_value_image_filter_correct
        delete_node_def
        split: option.split if_split_asm option.split_asm)

    thus "gbm_invar (gbm_delete_node v g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_delete_node_def delete_node_def 
      apply (auto simp: restrict_map_def option_bind_alt
        m1.correct m2.correct s3.correct m1.map_value_image_filter_correct
        split: option.split if_split_asm option.split_asm elim!: ranE)
      done
  qed

  lemma gbm_add_edge_impl:
    "graph_add_edge gbm_\<alpha> gbm_invar gbm_add_edge"
  proof
    fix g v e v'
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_add_edge v e v' g) = add_edge v e v' (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_add_edge_def
      apply (auto simp: m1.correct m2.correct s3.correct 
        Let_def
        split: option.split if_split_asm)
      unfolding add_edge_def
      (* Strange: This is at the limit of auto's capabilities:
        Iterated auto [] works., but auto on all goals seems not to
        terminate. Using fastforce instead.
        *)
      apply (fastforce split: if_split_asm
        simp: m1.correct m2.correct s3.correct 
      )+
      done
    
    thus "gbm_invar (gbm_add_edge v e v' g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_add_edge_def
      apply (force simp: m1.correct m2.correct s3.correct
        Let_def
        split: option.split if_split_asm elim!: ranE)
      done
  qed

  lemma gbm_delete_edge_impl:
    "graph_delete_edge gbm_\<alpha> gbm_invar gbm_delete_edge"
  proof
    fix g v e v'
    assume INV: "gbm_invar g"
    note [simp]= gbm_invar_split[OF INV]
    show "gbm_\<alpha> (gbm_delete_edge v e v' g) = delete_edge v e v' (gbm_\<alpha> g)"
      unfolding gbm_\<alpha>_def gbm_delete_edge_def delete_edge_def
      apply (auto simp: m1.correct m2.correct s3.correct 
        Let_def
        split: option.split if_split_asm)
      done
    
    thus "gbm_invar (gbm_delete_edge v e v' g)"  
      unfolding gbm_invar_def
      apply (simp)
      unfolding gbm_\<alpha>_def gbm_delete_edge_def
      apply (auto simp: m1.correct m2.correct s3.correct
        Let_def
        split: option.split if_split_asm elim!: ranE)
      done
  qed

  lemma gbm_nodes_list_it_impl:
    shows "graph_nodes_it gbm_\<alpha> gbm_invar gbm_nodes_list_it"
  proof 
    fix g
    assume "gbm_invar g"
    hence MINV: "map_op_invar m1_ops g" unfolding gbm_invar_def by auto
    from map_iterator_dom_correct[OF m1.iteratei_correct[OF MINV]]
    show "set_iterator (gbm_nodes_list_it g) (nodes (gbm_\<alpha> g))"
      unfolding gbm_nodes_list_it_def gbm_\<alpha>_def by simp
  qed
    
  lemma gbm_edges_list_it_impl:
    shows "graph_edges_it gbm_\<alpha> gbm_invar gbm_edges_list_it"
  proof 
    fix g
    assume INV: "gbm_invar g"

    from INV have I1: "m1.invar g" unfolding gbm_invar_def by auto
    from INV have I2: "\<And>v m2. (v,m2)\<in>map_to_set (m1.\<alpha> g) \<Longrightarrow> m2.invar m2"
      unfolding gbm_invar_def map_to_set_def
      by (auto simp: ran_def)
    from INV have I3: "\<And>v m2 v' s. \<lbrakk>
      (v,m2)\<in>map_to_set (m1.\<alpha> g); 
      (v',s)\<in>map_to_set (m2.\<alpha> m2)\<rbrakk> 
      \<Longrightarrow> s3.invar s"
      unfolding gbm_invar_def map_to_set_def
      by (auto simp: ran_def)

    show "set_iterator (gbm_edges_list_it g) (edges (gbm_\<alpha> g))"
      unfolding gbm_edges_list_it_def
      apply (rule set_iterator_image_correct)
      apply (rule set_iterator_product_correct)
      apply (rule m1.iteratei_correct)
      apply (rule I1)
      apply (case_tac a)
      apply clarsimp
      apply (rule set_iterator_product_correct)
      apply (drule I2)
      apply (subgoal_tac "map_iterator (m2.iteratei ba) 
        (map_op_\<alpha> m2_ops (snd (aa,ba)))")
      apply assumption
      apply (simp add: m2.iteratei_correct)

      apply (case_tac a)
      apply clarsimp
      apply (subgoal_tac "set_iterator (s3.iteratei bb) 
        (s3.\<alpha> (snd (ab,bb)))")
      apply assumption
      apply (simp add: s3.iteratei_correct I3)
      
      apply (auto simp: inj_on_def map_to_set_def) []

      apply (force simp: gbm_\<alpha>_def map_to_set_def) []
      done
    qed

  lemma gbm_succ_list_it_impl:
    shows "graph_succ_it gbm_\<alpha> gbm_invar gbm_succ_list_it"
  proof 
    fix g v
    assume INV: "gbm_invar g"
    hence I1[simp]: "m1.invar g" unfolding gbm_invar_def by auto

    show "set_iterator (gbm_succ_list_it g v) (succ (gbm_\<alpha> g) v)"
    proof (cases "m1.lookup v g")
      case None hence "(succ (gbm_\<alpha> g) v) = {}"
        unfolding succ_def gbm_\<alpha>_def by (auto simp: m1.lookup_correct)
      with None show ?thesis unfolding gbm_succ_list_it_def
        by (auto simp: set_iterator_emp_correct)
    next
      case (Some m2)
      hence [simp]: "m2.invar m2" using gbm_invar_split[OF INV] 
        by (simp add: m1.lookup_correct)

      from INV Some have 
        I2: "\<And>v' s. (v', s) \<in> map_to_set (map_op_\<alpha> m2_ops m2) \<Longrightarrow> s3.invar s"
        unfolding gbm_invar_def
        by (auto simp: map_to_set_def ran_def m1.lookup_correct)
      
      from Some show ?thesis
        unfolding gbm_succ_list_it_def apply simp
        apply (rule set_iterator_image_correct)
        apply (rule set_iterator_product_correct)
        apply (rule m2.iteratei_correct)
        apply simp
        apply (case_tac a, simp)
        apply (subgoal_tac "set_iterator (s3.iteratei b) (s3.\<alpha> (snd (aa, b)))")
        apply assumption
        apply simp
        apply (rule s3.iteratei_correct)
        apply (simp add: I2)

        apply (auto simp: inj_on_def map_to_set_def) []

        apply (force simp: succ_def gbm_\<alpha>_def map_to_set_def m1.lookup_correct)
        done
    qed
  qed
    
  lemma gbm_from_list_impl:
    shows "graph_from_list gbm_\<alpha> gbm_invar gbm_from_list"
    unfolding gbm_from_list_def
    apply (rule gga_from_list_correct)
    apply (rule gbm_empty_impl gbm_add_node_impl gbm_add_edge_impl)+
    done
  
end


sublocale GraphByMap < graph_nodes_it gbm_\<alpha> gbm_invar gbm_nodes_list_it 
  by (rule gbm_nodes_list_it_impl)
sublocale GraphByMap < graph_edges_it gbm_\<alpha> gbm_invar gbm_edges_list_it 
  by (rule gbm_edges_list_it_impl)
sublocale GraphByMap < graph_succ_it gbm_\<alpha> gbm_invar gbm_succ_list_it 
  by (rule gbm_succ_list_it_impl)

sublocale GraphByMap
  < gga_to_list_loc gbm_\<alpha> gbm_invar gbm_nodes_list_it gbm_edges_list_it 
  by unfold_locales

context GraphByMap
begin
  lemma gbm_to_list_impl: "graph_to_list gbm_\<alpha> gbm_invar gga_to_list"
    by (rule gga_to_list_correct)

  lemma gbm_ops_impl: "StdGraph gbm_ops"
    apply (rule StdGraph.intro)
    apply (simp_all add: icf_rec_unf)
    apply icf_locales
    apply (rule gbm_empty_impl gbm_add_node_impl gbm_delete_node_impl 
      gbm_add_edge_impl gbm_delete_edge_impl gbm_from_list_impl
      gbm_to_list_impl)+
    done
end

setup \<open>
  (Record_Intf.add_unf_thms_global @{thms 
    GraphByMapDefs.gbm_nodes_list_it_unf
    GraphByMapDefs.gbm_edges_list_it_unf
    GraphByMapDefs.gbm_succ_list_it_unf
  })
\<close> 
   
end
