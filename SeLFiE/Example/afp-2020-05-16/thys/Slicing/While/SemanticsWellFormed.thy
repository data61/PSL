section \<open>Semantic well-formedness of While CFG\<close>

theory SemanticsWellFormed 
  imports WellFormed WEquivalence "../Basic/SemanticsCFG" 
begin

subsection \<open>Instatiation of the \<open>CFG_semantics_wf\<close> locale\<close>

fun labels_nodes :: "cmd \<Rightarrow> w_node \<Rightarrow> cmd \<Rightarrow> bool" where
  "labels_nodes prog (_ l _) c     = labels prog l c"
  | "labels_nodes prog (_Entry_) c = False"
  | "labels_nodes prog (_Exit_) c  = False"


interpretation While_semantics_CFG_wf: CFG_semantics_wf 
  sourcenode targetnode kind "valid_edge prog" Entry reds "labels_nodes prog"
  for prog
proof(unfold_locales)
  fix n c s c' s' n'
  assume "labels_nodes prog n c" and "\<langle>c,s\<rangle> \<rightarrow>* \<langle>c',s'\<rangle>"
  then obtain l l' where [simp]:"n = (_ l _)" and "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle>"
    and "labels prog l' c'" by(cases n,auto dest:reds_steps)
  from \<open>labels prog l' c'\<close> have "l' < #:prog" by(rule label_less_num_inner_nodes)
  from \<open>prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto>* \<langle>c',s',l'\<rangle>\<close> 
  have "\<exists>as. CFG.path sourcenode targetnode (valid_edge prog)
    (_ l _) as (_ l' _) \<and>
    transfers (CFG.kinds kind as) s = s' \<and> preds (CFG.kinds kind as) s"
    proof(induct rule:converse_rtranclp_induct3)
      case refl
      from \<open>l' < #:prog\<close> have "valid_node prog (_ l' _)"
        by(fastforce dest:less_num_nodes_edge simp:valid_node_def valid_edge_def)
      hence "CFG.valid_node sourcenode targetnode (valid_edge prog) (_ l' _)"
        by(simp add:valid_node_def While_CFG.valid_node_def)
      hence "CFG.path sourcenode targetnode (valid_edge prog) (_ l' _) [] (_ l' _)"
        by(rule While_CFG.empty_path)
      thus ?case by(auto simp:While_CFG.kinds_def)
    next
      case (step c s l c'' s'' l'')
      from \<open>(\<lambda>(c, s, l) (c', s', l'). 
        prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c',s',l'\<rangle>) (c,s,l) (c'',s'',l'')\<close>
      have "prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s'',l''\<rangle>" by simp
      from \<open>\<exists>as. CFG.path sourcenode targetnode (valid_edge prog)
        (_ l'' _) as (_ l' _) \<and>
       transfers (CFG.kinds kind as) s'' = s' \<and>
       preds (CFG.kinds kind as) s''\<close>
      obtain as where "CFG.path sourcenode targetnode (valid_edge prog)
        (_ l'' _) as (_ l' _)"
        and "transfers (CFG.kinds kind as) s'' = s'"
        and "preds (CFG.kinds kind as) s''" by auto
      from \<open>prog \<turnstile> \<langle>c,s,l\<rangle> \<leadsto> \<langle>c'',s'',l''\<rangle>\<close> obtain et 
        where "prog \<turnstile> (_ l _) -et\<rightarrow> (_ l'' _)"
        and "transfer et s = s''" and "pred et s"
        by(erule step_WCFG_edge)
      from \<open>prog \<turnstile> (_ l _) -et\<rightarrow> (_ l'' _)\<close>
        \<open>CFG.path sourcenode targetnode (valid_edge prog) (_ l'' _) as (_ l' _)\<close> 
      have "CFG.path sourcenode targetnode (valid_edge prog)
        (_ l _) (((_ l _),et,(_ l'' _))#as) (_ l' _)"
        by(fastforce intro:While_CFG.Cons_path simp:valid_edge_def)
      moreover
      from \<open>transfers (CFG.kinds kind as) s'' = s'\<close> \<open>transfer et s = s''\<close>
      have "transfers (CFG.kinds kind (((_ l _),et,(_ l'' _))#as)) s = s'"
        by(simp add:While_CFG.kinds_def)
      moreover from \<open>preds (CFG.kinds kind as) s''\<close> \<open>pred et s\<close> \<open>transfer et s = s''\<close>
      have "preds (CFG.kinds kind (((_ l _),et,(_ l'' _))#as)) s"
        by(simp add:While_CFG.kinds_def)
      ultimately show ?case by blast
    qed
  with \<open>labels prog l' c'\<close>
  show "(\<exists>n' as. 
         CFG.path sourcenode targetnode (valid_edge prog) n as n' \<and>
         transfers (CFG.kinds kind as) s = s' \<and>
         preds (CFG.kinds kind as) s \<and> labels_nodes prog n' c')"
    by(rule_tac x="(_ l' _)" in exI,simp)
qed

end
