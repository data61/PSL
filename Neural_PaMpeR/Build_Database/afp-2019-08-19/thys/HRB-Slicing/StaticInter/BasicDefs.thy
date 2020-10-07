chapter \<open>The Framework\<close>

theory BasicDefs imports AuxLemmas begin

text \<open>
  As slicing is a program analysis that can be completely based on the
  information given in the CFG, we want to provide a framework which
  allows us to formalize and prove properties of slicing regardless of
  the actual programming language. So the starting point for the formalization 
  is the definition of an abstract CFG, i.e.\ without considering features 
  specific for certain languages. By doing so we ensure that our framework 
  is as generic as possible since all proofs hold for every language whose 
  CFG conforms to this abstract CFG.

  Static Slicing analyses a CFG prior to execution. Whereas dynamic
  slicing can provide better results for certain inputs (i.e.\ trace and
  initial state), static slicing is more conservative but provides
  results independent of inputs. 

  Correctness for static slicing is defined using a weak
  simulation between nodes and states when traversing the original and
  the sliced graph. The weak simulation property demands that if a
  (node,state) tuples $(n_1,s_1)$ simulates $(n_2,s_2)$
  and making an observable move in the original graph leads from 
  $(n_1,s_1)$ to $(n_1',s_1')$, this tuple simulates a 
  tuple $(n_2,s_2)$ which is the result of making an
  observable move in the sliced graph beginning in $(n_2',s_2')$.  
\<close>

section \<open>Basic Definitions\<close>

fun fun_upds :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> 'b)"
where "fun_upds f [] ys = f"
  | "fun_upds f xs [] = f"
  | "fun_upds f (x#xs) (y#ys) = (fun_upds f xs ys)(x := y)"

notation fun_upds ("_'(_ /[:=]/ _')")

lemma fun_upds_nth:
  "\<lbrakk>i < length xs; length xs = length ys; distinct xs\<rbrakk>
  \<Longrightarrow> f(xs [:=] ys)(xs!i) = (ys!i)"
proof(induct xs arbitrary:ys i)
  case Nil thus ?case by simp
next
  case (Cons x' xs')
  note IH = \<open>\<And>ys i. \<lbrakk>i < length xs'; length xs' = length ys; distinct xs'\<rbrakk>
    \<Longrightarrow> f(xs' [:=] ys) (xs'!i) = ys!i\<close>
  from \<open>distinct (x'#xs')\<close> have "distinct xs'" and "x' \<notin> set xs'" by simp_all
  from \<open>length (x'#xs') = length ys\<close> obtain y' ys' where [simp]:"ys = y'#ys'"
    and "length xs' = length ys'"
    by(cases ys) auto
  show ?case
  proof(cases i)
    case 0 thus ?thesis by simp
  next
    case (Suc j)
    with \<open>i < length (x'#xs')\<close> have "j < length xs'" by simp
    from IH[OF this \<open>length xs' = length ys'\<close> \<open>distinct xs'\<close>]
    have "f(xs' [:=] ys') (xs'!j) = ys'!j" .
    with \<open>x' \<notin> set xs'\<close> \<open>j < length xs'\<close>
    have "f((x'#xs') [:=] ys) ((x'#xs')!(Suc j)) = ys!(Suc j)" by fastforce
    with Suc show ?thesis by simp
  qed
qed


lemma fun_upds_eq:
  assumes "V \<in> set xs" and "length xs = length ys" and "distinct xs"
  shows "f(xs [:=] ys) V = f'(xs [:=] ys) V"
proof -
  from \<open>V \<in> set xs\<close> obtain i where "i < length xs" and "xs!i = V"
    by(fastforce simp:in_set_conv_nth)
  with \<open>length xs = length ys\<close> \<open>distinct xs\<close>
  have "f(xs [:=] ys)(xs!i) = (ys!i)" by -(rule fun_upds_nth)
  moreover
  from \<open>i < length xs\<close> \<open>xs!i = V\<close> \<open>length xs = length ys\<close> \<open>distinct xs\<close>
  have "f'(xs [:=] ys)(xs!i) = (ys!i)" by -(rule fun_upds_nth)
  ultimately show ?thesis using \<open>xs!i = V\<close> by simp
qed


lemma fun_upds_notin:"x \<notin> set xs \<Longrightarrow> f(xs [:=] ys) x = f x"
by(induct xs arbitrary:ys,auto,case_tac ys,auto)


subsection \<open>\<open>distinct_fst\<close>\<close>
 
definition distinct_fst :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "distinct_fst  \<equiv>  distinct \<circ> map fst"

lemma distinct_fst_Nil [simp]:
  "distinct_fst []" 
  by(simp add:distinct_fst_def)

lemma distinct_fst_Cons [simp]:
  "distinct_fst ((k,x)#kxs) = (distinct_fst kxs \<and> (\<forall>y. (k,y) \<notin> set kxs))"
by(auto simp:distinct_fst_def image_def)


lemma distinct_fst_isin_same_fst:
  "\<lbrakk>(x,y) \<in> set xs; (x,y') \<in> set xs; distinct_fst xs\<rbrakk>
  \<Longrightarrow> y = y'"
by(induct xs,auto simp:distinct_fst_def image_def)


subsection\<open>Edge kinds\<close>

text \<open>Every procedure has a unique name, e.g. in object oriented languages
  \<open>pname\<close> refers to class + procedure.\<close>

text \<open>A state is a call stack of tuples, which consists of:
  \begin{enumerate}
  \item data information, i.e.\ a mapping from the local variables in the call 
  frame to their values, and
  \item control flow information, e.g.\ which node called the current procedure.
  \end{enumerate}

  Update and predicate edges check and manipulate only the data information
  of the top call stack element. Call and return edges however may use the data and
  control flow information present in the top stack element to state if this edge is
  traversable. The call edge additionally has a list of functions to determine what
  values the parameters have in a certain call frame and control flow information for
  the return. The return edge is concerned with passing the values 
  of the return parameter values to the underlying stack frame. See the funtions 
  \<open>transfer\<close> and \<open>pred\<close> in locale \<open>CFG\<close>.\<close>

datatype (dead 'var, dead 'val, dead 'ret, dead 'pname) edge_kind =
    UpdateEdge "('var \<rightharpoonup> 'val) \<Rightarrow> ('var \<rightharpoonup> 'val)"                  ("\<Up>_")
  | PredicateEdge "('var \<rightharpoonup> 'val) \<Rightarrow> bool"                         ("'(_')\<^sub>\<surd>")
  | CallEdge "('var \<rightharpoonup> 'val) \<times> 'ret \<Rightarrow> bool" "'ret" "'pname"  
             "(('var \<rightharpoonup> 'val) \<rightharpoonup> 'val) list"                       ("_:_\<hookrightarrow>\<^bsub>_\<^esub>_" 70)
  | ReturnEdge "('var \<rightharpoonup> 'val) \<times> 'ret \<Rightarrow> bool" "'pname" 
               "('var \<rightharpoonup> 'val) \<Rightarrow> ('var \<rightharpoonup> 'val) \<Rightarrow> ('var \<rightharpoonup> 'val)" ("_\<hookleftarrow>\<^bsub>_\<^esub>_" 70)


definition intra_kind :: "('var,'val,'ret,'pname) edge_kind \<Rightarrow> bool"
where "intra_kind et \<equiv> (\<exists>f. et = \<Up>f) \<or> (\<exists>Q. et = (Q)\<^sub>\<surd>)"


lemma edge_kind_cases [case_names Intra Call Return]:
  "\<lbrakk>intra_kind et \<Longrightarrow> P; \<And>Q r p fs. et = Q:r\<hookrightarrow>\<^bsub>p\<^esub>fs \<Longrightarrow> P;
    \<And>Q p f. et = Q\<hookleftarrow>\<^bsub>p\<^esub>f \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
by(cases et,auto simp:intra_kind_def)


end
