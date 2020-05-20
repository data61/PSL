theory SestoftCorrect
imports BalancedTraces Launchbury.Launchbury Sestoft
begin


lemma lemma_2:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e, S) \<subseteq> set L \<union> domA \<Gamma>"
  shows "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, S)"
using assms
proof(induction arbitrary: S  rule:reds.induct)
  case (Lambda \<Gamma> x e L)
  show ?case..
next
  case (Application y \<Gamma> e x L \<Delta> \<Theta> z e')
  from \<open>fv (\<Gamma>, App e x, S) \<subseteq> set L \<union> domA \<Gamma>\<close>
  have prem1: "fv (\<Gamma>, e, Arg x # S) \<subseteq> set L \<union> domA \<Gamma>" by simp
  
  from prem1 reds_pres_closed[OF \<open>\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : Lam [y]. e'\<close>] reds_doesnt_forget[OF \<open>\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : Lam [y]. e'\<close>]
  have prem2: "fv (\<Delta>, e'[y::=x], S) \<subseteq> set L \<union> domA \<Delta>" by (auto simp add: fv_subst_eq)

  have "(\<Gamma>, App e x, S) \<Rightarrow> (\<Gamma>, e, Arg x # S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, Lam [y]. e', Arg x# S)" by (rule Application.IH(1)[OF prem1])
  also have "\<dots> \<Rightarrow> (\<Delta>, e'[y ::= x], S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Theta>, z, S)" by (rule Application.IH(2)[OF prem2])
  finally show ?case.
next
case (Variable \<Gamma> x e L \<Delta> z S)
  from Variable(2)
  have "isVal z" by (rule result_evaluated)

  have "x \<notin> domA \<Delta>" by (rule reds_avoids_live[OF Variable(2), where x = x]) simp_all

  from \<open>fv (\<Gamma>, Var x, S) \<subseteq> set L \<union> domA \<Gamma>\<close>
  have prem: "fv (delete x \<Gamma>, e, Upd x # S) \<subseteq> set (x#L) \<union> domA (delete x \<Gamma>)"
    by (auto dest: subsetD[OF fv_delete_subset] subsetD[OF map_of_Some_fv_subset[OF \<open>map_of \<Gamma> x = Some e\<close>]])

  from \<open>map_of \<Gamma> x = Some e\<close>
  have "(\<Gamma>, Var x, S) \<Rightarrow> (delete x \<Gamma>, e, Upd x # S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, Upd x # S)" by (rule Variable.IH[OF prem])
  also have "\<dots> \<Rightarrow> ((x,z)#\<Delta>, z, S)" using \<open>x \<notin> domA \<Delta>\<close> \<open>isVal z\<close> by (rule var\<^sub>2)
  finally show ?case.
next
case (Bool \<Gamma> b L S)
  show ?case..
next
case (IfThenElse \<Gamma> scrut L \<Delta> b e\<^sub>1 e\<^sub>2 \<Theta> z S)
  have "(\<Gamma>, scrut ? e\<^sub>1 : e\<^sub>2, S) \<Rightarrow> (\<Gamma>, scrut, Alts e\<^sub>1 e\<^sub>2 #S)"..
  also
  from IfThenElse.prems
  have prem1: "fv (\<Gamma>, scrut, Alts e\<^sub>1 e\<^sub>2 #S) \<subseteq> set L \<union> domA \<Gamma>" by auto
  hence "(\<Gamma>, scrut, Alts e\<^sub>1 e\<^sub>2 #S) \<Rightarrow>\<^sup>* (\<Delta>, Bool b, Alts e\<^sub>1 e\<^sub>2 #S)"
    by (rule IfThenElse.IH)
  also
  have "(\<Delta>, Bool b, Alts e\<^sub>1 e\<^sub>2 #S) \<Rightarrow> (\<Delta>, if b then e\<^sub>1 else e\<^sub>2, S)"..
  also
  from prem1 reds_pres_closed[OF IfThenElse(1)] reds_doesnt_forget[OF IfThenElse(1)]
  have prem2: "fv (\<Delta>, if b then e\<^sub>1 else e\<^sub>2, S) \<subseteq> set L \<union> domA \<Delta>"  by auto
  hence "(\<Delta>, if b then e\<^sub>1 else e\<^sub>2, S) \<Rightarrow>\<^sup>* (\<Theta>, z, S)" by (rule IfThenElse.IH(2))
  finally
  show ?case.
next
case (Let as \<Gamma> L body \<Delta> z S)
  from Let(4)
  have prem: "fv (as @ \<Gamma>, body, S) \<subseteq> set L \<union> domA (as @ \<Gamma>)" by auto

  from Let(1) 
  have "atom ` domA as \<sharp>* \<Gamma>" by (auto simp add: fresh_star_Pair)
  moreover
  from Let(1)
  have "domA as \<inter> fv (\<Gamma>, L) = {}"
    by (rule fresh_distinct_fv)
  hence "domA as \<inter> (set L \<union> domA \<Gamma>) = {}"
    by (auto dest: subsetD[OF domA_fv_subset])
  with Let(4)
  have "domA as \<inter> fv S = {}"
    by auto
  hence "atom ` domA as \<sharp>* S"
    by (auto simp add: fresh_star_def fv_def fresh_def)
  ultimately
  have "(\<Gamma>, Terms.Let as body, S) \<Rightarrow> (as@\<Gamma>, body, S)"..
  also have "\<dots> \<Rightarrow>\<^sup>* (\<Delta>, z, S)"
    by (rule Let.IH[OF prem])
  finally show ?case.
qed

type_synonym trace = "conf list"

fun stack :: "conf \<Rightarrow> stack" where "stack (\<Gamma>, e, S) = S"
                 
interpretation traces step.

abbreviation trace_syn ("_ \<Rightarrow>\<^sup>*\<^bsub>_\<^esub> _" [50,50,50] 50) where "trace_syn \<equiv> trace"

lemma conf_trace_induct_final[consumes 1, case_names trace_nil trace_cons]:
  "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> final \<Longrightarrow> (\<And> \<Gamma> e S. final = (\<Gamma>, e, S) \<Longrightarrow> P \<Gamma> e S [] (\<Gamma>, e, S)) \<Longrightarrow> (\<And>\<Gamma> e S T \<Gamma>' e' S'. (\<Gamma>', e', S') \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> final \<Longrightarrow> P \<Gamma>' e' S' T final \<Longrightarrow> (\<Gamma>, e, S) \<Rightarrow> (\<Gamma>', e', S') \<Longrightarrow> P \<Gamma> e S ((\<Gamma>', e', S') # T) final) \<Longrightarrow> P \<Gamma> e S T final"
  by (induction "(\<Gamma>, e, S)" T final arbitrary: \<Gamma> e S rule: trace_induct_final) auto

interpretation balance_trace step  stack
  apply standard
  apply (erule step.cases)
  apply auto
  done

abbreviation bal_syn ("_ \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>_\<^esub> _" [50,50,50] 50) where "bal_syn \<equiv> bal"

lemma isVal_stops:
  assumes "isVal e"
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
  shows "T=[]"
  using assms
  apply -
  apply (erule balE)
  apply (erule trace.cases)
  apply simp
  apply auto
  apply (auto elim!: step.cases)
  done

 
lemma Ball_subst[simp]:
  "(\<forall>p\<in>set (\<Gamma>[y::h=x]). f p) \<longleftrightarrow> (\<forall>p\<in>set \<Gamma>. case p of (z,e) \<Rightarrow> f (z, e[y::=x]))"
  by (induction \<Gamma>) auto

lemma lemma_3:
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
  assumes "isVal z"
  shows "\<Gamma> : e \<Down>\<^bsub>upds_list S\<^esub> \<Delta> : z"
using assms
proof(induction T arbitrary: \<Gamma> e S \<Delta> z rule: measure_induct_rule[where f = length])
  case (less T \<Gamma> e S \<Delta> z)
  from \<open>(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)\<close>
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)" and "\<forall> c'\<in>set T. S \<lesssim> stack c'" unfolding bal.simps by auto

  from this(1)
  show ?case
  proof(cases)
  case trace_nil
    from \<open>isVal z\<close>  trace_nil show ?thesis by (auto intro: reds_isValI)
  next
  case (trace_cons conf' T')
    from \<open>T = conf' # T'\<close> and \<open>\<forall> c'\<in>set T. S \<lesssim> stack c'\<close> have "S \<lesssim> stack conf'" by auto

    from \<open>(\<Gamma>, e, S) \<Rightarrow> conf'\<close>
    show ?thesis
    proof(cases)
    case (app\<^sub>1 e x)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "(\<Gamma>, e, Arg x # S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>1\<^esub> c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: " c\<^sub>4 \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>2\<^esub> (\<Delta>, z, S)"
        by (rule bal_consE[OF  \<open>bal _ T _\<close>[unfolded app\<^sub>1 trace_cons]]) (simp, rule)

      from \<open>T = _\<close> \<open>T' = _\<close> have "length T\<^sub>1 < length T" and "length T\<^sub>2 < length T" by auto

      from prem1 have "stack c\<^sub>3 =  Arg x # S" by (auto dest:  bal_stackD)
      moreover
      from prem2 have "stack c\<^sub>4 = S" by (auto dest: bal_stackD)
      moreover
      note \<open>c\<^sub>3 \<Rightarrow> c\<^sub>4\<close>
      ultimately
      obtain \<Delta>' y e' where "c\<^sub>3 = (\<Delta>', Lam [y]. e', Arg x # S)" and "c\<^sub>4 = (\<Delta>', e'[y ::= x], S)"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)

      
      from less(1)[OF \<open>length T\<^sub>1 < length T\<close> prem1[unfolded \<open>c\<^sub>3 = _\<close> \<open>c\<^sub>4 = _\<close>]]
      have "\<Gamma> : e \<Down>\<^bsub>upds_list S\<^esub> \<Delta>' : Lam [y]. e'" by simp
      moreover
      from less(1)[OF \<open>length T\<^sub>2 < length T\<close> prem2[unfolded \<open>c\<^sub>3 = _\<close> \<open>c\<^sub>4 = _\<close>] \<open>isVal z\<close>]
      have "\<Delta>' : e'[y::=x] \<Down>\<^bsub>upds_list S\<^esub> \<Delta> : z" by simp
      ultimately
      show ?thesis unfolding app\<^sub>1
        by (rule reds_ApplicationI)
    next
    case (app\<^sub>2 y e x S')
      from \<open>conf' =_\<close> \<open>S = _ # S'\<close> \<open>S \<lesssim> stack conf'\<close>
      have False by (auto simp add: extends_def)
      thus ?thesis..
    next
    case (var\<^sub>1 x e)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "(delete x \<Gamma>, e, Upd x # S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>1\<^esub> c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: "c\<^sub>4 \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>2\<^esub> (\<Delta>, z, S)"
        by (rule bal_consE[OF  \<open>bal _ T _\<close>[unfolded var\<^sub>1 trace_cons]]) (simp, rule)
      
      from \<open>T = _\<close> \<open>T' = _\<close> have "length T\<^sub>1 < length T" and "length T\<^sub>2 < length T" by auto

      from prem1 have "stack c\<^sub>3 = Upd x # S" by (auto dest:  bal_stackD)
      moreover
      from prem2 have "stack c\<^sub>4 = S" by (auto dest: bal_stackD)
      moreover
      note \<open>c\<^sub>3 \<Rightarrow> c\<^sub>4\<close>
      ultimately
      obtain \<Delta>' z' where "c\<^sub>3 = (\<Delta>', z', Upd x # S)" and "c\<^sub>4 = ((x,z')#\<Delta>', z', S)" and "isVal z'"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)

      from \<open>isVal z'\<close> and prem2[unfolded \<open>c\<^sub>4 = _\<close>]
      have "T\<^sub>2 = []" by (rule isVal_stops)
      with prem2 \<open>c\<^sub>4 = _\<close>
      have "z' = z" and "\<Delta> = (x,z)#\<Delta>'" by auto
          
      from less(1)[OF \<open>length T\<^sub>1 < length T\<close> prem1[unfolded \<open>c\<^sub>3 = _\<close> \<open>c\<^sub>4 = _\<close>  \<open>z' = _\<close>]  \<open>isVal z\<close>]
      have "delete x \<Gamma> : e \<Down>\<^bsub>x # upds_list S\<^esub> \<Delta>' : z" by simp
      with \<open>map_of _ _ = _\<close>
      show ?thesis unfolding var\<^sub>1(1) \<open>\<Delta> = _\<close> by rule
    next
    case (var\<^sub>2 x S')
      from \<open>conf' = _\<close> \<open>S = _ # S'\<close> \<open>S \<lesssim> stack conf'\<close>
      have False by (auto simp add: extends_def)
      thus ?thesis..
    next
    case (if\<^sub>1 scrut  e\<^sub>1 e\<^sub>2)
      obtain T\<^sub>1 c\<^sub>3 c\<^sub>4 T\<^sub>2
      where "T' = T\<^sub>1 @ c\<^sub>4 # T\<^sub>2" and prem1: "(\<Gamma>, scrut, Alts e\<^sub>1 e\<^sub>2 # S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>1\<^esub> c\<^sub>3" and "c\<^sub>3 \<Rightarrow> c\<^sub>4" and prem2: "c\<^sub>4 \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^sub>2\<^esub> (\<Delta>, z, S)"
        by (rule bal_consE[OF  \<open>bal _ T _\<close>[unfolded if\<^sub>1 trace_cons]])  (simp, rule)

      from \<open>T = _\<close> \<open>T' = _\<close> have "length T\<^sub>1 < length T" and "length T\<^sub>2 < length T" by auto

      from prem1 have "stack c\<^sub>3 = Alts e\<^sub>1 e\<^sub>2 # S" by (auto dest:  bal_stackD)
      moreover
      from prem2 have "stack c\<^sub>4 = S" by (auto dest: bal_stackD)
      moreover
      note \<open>c\<^sub>3 \<Rightarrow> c\<^sub>4\<close>
      ultimately
      obtain \<Delta>' b where "c\<^sub>3 = (\<Delta>', Bool b, Alts e\<^sub>1 e\<^sub>2 # S)" and "c\<^sub>4 = (\<Delta>', (if b then e\<^sub>1 else e\<^sub>2), S)"
        by (auto elim!: step.cases simp del: exp_assn.eq_iff)

      from less(1)[OF \<open>length T\<^sub>1 < length T\<close> prem1[unfolded \<open>c\<^sub>3 = _\<close> \<open>c\<^sub>4 = _\<close> ] isVal_Bool]
      have "\<Gamma> : scrut \<Down>\<^bsub>upds_list S\<^esub> \<Delta>' : Bool b" by simp
      moreover
      from less(1)[OF \<open>length T\<^sub>2 < length T\<close> prem2[unfolded \<open>c\<^sub>4 = _\<close>] \<open>isVal z\<close>]
      have "\<Delta>' : (if b then e\<^sub>1 else e\<^sub>2) \<Down>\<^bsub>upds_list S\<^esub> \<Delta> : z".
      ultimately
      show ?thesis unfolding if\<^sub>1 by (rule reds.IfThenElse)
   next
    case (if\<^sub>2 b e1 e2 S')
      from \<open>conf' = _\<close> \<open>S = _ # S'\<close> \<open>S \<lesssim> stack conf'\<close>
      have False by (auto simp add: extends_def)
      thus ?thesis..
    next
    case (let\<^sub>1 as e)
      from \<open>T = conf' # T'\<close> have "length T' < length T" by auto
      moreover
      have "(as @ \<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T'\<^esub> (\<Delta>, z, S)" 
        using trace_cons \<open>conf' = _\<close>  \<open>\<forall> c'\<in>set T. S \<lesssim> stack c'\<close> by fastforce
      moreover
      note \<open>isVal z\<close>
      ultimately
      have "as @ \<Gamma> : e \<Down>\<^bsub>upds_list S\<^esub> \<Delta> : z" by (rule less)
      moreover
      from \<open>atom ` domA as \<sharp>* \<Gamma>\<close>  \<open>atom ` domA as \<sharp>* S\<close>
      have "atom ` domA as \<sharp>* (\<Gamma>, upds_list S)" by (auto simp add: fresh_star_Pair)
      ultimately
      show ?thesis unfolding let\<^sub>1  by (rule reds.Let[rotated])
    qed
  qed
qed

lemma dummy_stack_extended:
  "set S \<subseteq>  Dummy ` UNIV \<Longrightarrow> x \<notin> Dummy ` UNIV \<Longrightarrow> (S \<lesssim> x # S') \<longleftrightarrow>  S \<lesssim> S'"
  apply (auto simp add: extends_def)
  apply (case_tac S'')
  apply auto
  done

lemma[simp]: "Arg x \<notin> range Dummy"  "Upd x \<notin> range Dummy"   "Alts e\<^sub>1 e\<^sub>2 \<notin> range Dummy" by auto

lemma dummy_stack_balanced:
  assumes "set S \<subseteq> Dummy ` UNIV"
  assumes "(\<Gamma>, e, S) \<Rightarrow>\<^sup>* (\<Delta>, z, S)"
  obtains T where "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
proof-
  from build_trace[OF assms(2)]
  obtain T where "(\<Gamma>, e, S) \<Rightarrow>\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"..
  moreover
  hence "\<forall> c'\<in>set T. stack (\<Gamma>, e, S) \<lesssim> stack c'"
    by (rule conjunct1[OF traces_list_all])
       (auto elim: step.cases simp add: dummy_stack_extended[OF \<open>set S \<subseteq> Dummy ` UNIV\<close>])
  ultimately
  have "(\<Gamma>, e, S) \<Rightarrow>\<^sup>b\<^sup>*\<^bsub>T\<^esub> (\<Delta>, z, S)"
    by (rule balI) simp
  thus ?thesis by (rule that)
qed

end
