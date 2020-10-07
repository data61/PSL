theory Launchbury
imports Terms Substitution
begin

subsubsection \<open>The natural semantics\<close>

text \<open>This is the semantics as in \cite{launchbury}, with two differences:
\begin{itemize}
\item Explicit freshness requirements for bound variables in the application and the Let rule.
\item An additional parameter that stores variables that have to be avoided, but do not occur
in the judgement otherwise, follwing \cite{sestoft}.
\end{itemize}
\<close>

inductive
  reds :: "heap \<Rightarrow> exp \<Rightarrow> var list \<Rightarrow> heap \<Rightarrow> exp \<Rightarrow> bool"
  ("_ : _ \<Down>\<^bsub>_\<^esub> _ : _" [50,50,50,50] 50)
where
  Lambda:
    "\<Gamma> : (Lam [x]. e) \<Down>\<^bsub>L\<^esub> \<Gamma> : (Lam [x]. e)" 
 | Application: "\<lbrakk>
    atom y \<sharp> (\<Gamma>,e,x,L,\<Delta>,\<Theta>,z) ;
    \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : (Lam [y]. e');
    \<Delta> : e'[y ::= x] \<Down>\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : App e x \<Down>\<^bsub>L\<^esub> \<Theta> : z" 
 | Variable: "\<lbrakk>
    map_of \<Gamma> x = Some e; delete x \<Gamma> : e \<Down>\<^bsub>x#L\<^esub> \<Delta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Var x \<Down>\<^bsub>L\<^esub> (x, z) # \<Delta> : z"
 | Let: "\<lbrakk>
    atom ` domA \<Delta> \<sharp>* (\<Gamma>, L);
    \<Delta> @ \<Gamma> : body \<Down>\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : Let \<Delta> body \<Down>\<^bsub>L\<^esub> \<Theta> : z"
 | Bool:
    "\<Gamma> : Bool b \<Down>\<^bsub>L\<^esub> \<Gamma> : Bool b"
 | IfThenElse: "\<lbrakk>
    \<Gamma> : scrut \<Down>\<^bsub>L\<^esub> \<Delta> : (Bool b);
    \<Delta> : (if b then e\<^sub>1 else e\<^sub>2) \<Down>\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk>  \<Longrightarrow>
    \<Gamma> : (scrut ? e\<^sub>1 : e\<^sub>2) \<Down>\<^bsub>L\<^esub> \<Theta> : z"

equivariance reds

nominal_inductive reds
  avoids Application: "y"
  by (auto simp add: fresh_star_def fresh_Pair)

subsubsection \<open>Example evaluations\<close>

lemma eval_test:
  "[] : (Let [(x, Lam [y]. Var y)] (Var x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
apply(auto intro!: Lambda Application Variable Let
 simp add: fresh_Pair fresh_Cons fresh_Nil fresh_star_def)
done

lemma eval_test2:
  "y \<noteq> x \<Longrightarrow> n \<noteq> y \<Longrightarrow> n \<noteq> x \<Longrightarrow>[] : (Let [(x, Lam [y]. Var y)] (App (Var x) x)) \<Down>\<^bsub>[]\<^esub> [(x, Lam [y]. Var y)] : (Lam [y]. Var y)"
  by (auto intro!: Lambda Application Variable Let simp add: fresh_Pair fresh_at_base fresh_Cons fresh_Nil fresh_star_def pure_fresh)

subsubsection \<open>Better introduction rules\<close>

text \<open>
This variant do not require freshness.
\<close>

lemma reds_ApplicationI:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : Lam [y]. e'"
  assumes "\<Delta> : e'[y::=x] \<Down>\<^bsub>L\<^esub> \<Theta> : z"
  shows "\<Gamma> : App e x \<Down>\<^bsub>L\<^esub> \<Theta> : z"
proof-
  obtain y' :: var where "atom y' \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z, e')" by (rule obtain_fresh)

  have a: "Lam [y']. ((y' \<leftrightarrow> y) \<bullet> e') = Lam [y]. e'"
    using \<open>atom y' \<sharp> _\<close>
    by (auto simp add: Abs1_eq_iff fresh_Pair fresh_at_base)

  have b: "((y' \<leftrightarrow> y) \<bullet> e')[y'::=x] = e'[y::=x]"
  proof(cases "x = y")
    case True
    have "atom y' \<sharp> e'" using \<open>atom y' \<sharp> _\<close> by simp
    thus ?thesis
      by (simp add: True subst_swap_same  subst_subst_back)
  next
    case False
    hence "atom y \<sharp> x" by simp

    have [simp]: "(y' \<leftrightarrow> y) \<bullet> x = x" using \<open>atom y \<sharp> _\<close>  \<open>atom y' \<sharp> _\<close>
        by (simp add: flip_fresh_fresh fresh_Pair fresh_at_base)

    have "((y' \<leftrightarrow> y) \<bullet> e')[y'::=x] = (y' \<leftrightarrow> y) \<bullet> (e'[y::=x])" by simp
    also have "\<dots> = e'[y::=x]"
      using \<open>atom y \<sharp> _\<close>  \<open>atom y' \<sharp> _\<close>
      by (simp add: flip_fresh_fresh fresh_Pair fresh_at_base subst_pres_fresh)
    finally
    show ?thesis.
  qed
  have "atom y' \<sharp> (\<Gamma>, e, x, L, \<Delta>, \<Theta>, z)" using  \<open>atom y' \<sharp> _\<close> by (simp add: fresh_Pair)
  from this assms[folded a b]
  show ?thesis ..
qed

lemma reds_SmartLet: "\<lbrakk>
    atom ` domA \<Delta> \<sharp>* (\<Gamma>, L);
    \<Delta> @ \<Gamma> : body \<Down>\<^bsub>L\<^esub> \<Theta> : z
  \<rbrakk> \<Longrightarrow>
    \<Gamma> : SmartLet \<Delta> body \<Down>\<^bsub>L\<^esub> \<Theta> : z"
unfolding SmartLet_def
by (auto intro: reds.Let)

text \<open>
A single rule for values
\<close>
lemma reds_isValI:
  "isVal z \<Longrightarrow> \<Gamma> : z \<Down>\<^bsub>L\<^esub> \<Gamma> : z"
by (cases z rule:isVal.cases) (auto intro: reds.intros)


subsubsection \<open>Properties of the semantics\<close>

text \<open>
Heap entries are never removed.
\<close>

lemma reds_doesnt_forget:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> domA \<Gamma> \<subseteq> domA \<Delta>"
by(induct rule: reds.induct) auto

text \<open>
Live variables are not added to the heap.
\<close>

lemma reds_avoids_live':
 assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
 shows "(domA \<Delta> - domA \<Gamma>) \<inter> set L = {}"
using assms
by(induct rule:reds.induct)
  (auto dest: map_of_domAD fresh_distinct_list simp add: fresh_star_Pair)

lemma reds_avoids_live:
  "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> set L;
   x \<notin> domA \<Gamma>
  \<rbrakk> \<Longrightarrow> x \<notin> domA \<Delta>"
using reds_avoids_live' by blast

text \<open>
Fresh variables either stay fresh or are added to the heap.
\<close>

lemma reds_fresh:" \<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   atom (x::var) \<sharp> (\<Gamma>, e)
  \<rbrakk> \<Longrightarrow> atom x \<sharp> (\<Delta>, z) \<or> x \<in> (domA \<Delta> - set L)"
proof(induct rule: reds.induct)
case (Lambda \<Gamma> x e) thus ?case by auto
next
case (Application y \<Gamma> e x' L \<Delta> \<Theta> z e')
  hence "atom x \<sharp> (\<Delta>, Lam [y]. e') \<or> x \<in> domA \<Delta> - set (x' # L)" by (auto simp add: fresh_Pair)

  thus ?case
  proof
    assume  "atom x \<sharp> (\<Delta>, Lam [y]. e')"
    hence "atom x \<sharp> e'[y ::= x']"
      using Application.prems
      by (auto intro: subst_pres_fresh simp add: fresh_Pair)
    thus ?thesis using Application.hyps(5) \<open>atom x \<sharp> (\<Delta>, Lam [y]. e')\<close> by auto
  next
    assume "x \<in> domA \<Delta> - set (x' # L)"
    thus ?thesis using reds_doesnt_forget[OF Application.hyps(4)] by auto
  qed
next

case(Variable \<Gamma> v e L \<Delta> z)
  have "atom x \<sharp> \<Gamma>" and "atom x \<sharp> v" using Variable.prems(1) by (auto simp add: fresh_Pair)
  from fresh_delete[OF this(1)]
  have "atom x \<sharp> delete v \<Gamma>".
  moreover
  have "v \<in> domA \<Gamma>" using Variable.hyps(1) by (metis domA_from_set map_of_SomeD)
  from fresh_map_of[OF this  \<open>atom x \<sharp> \<Gamma>\<close>]
  have "atom x \<sharp> the (map_of \<Gamma> v)".
  hence "atom x \<sharp> e" using \<open>map_of \<Gamma> v = Some e\<close> by simp
  ultimately
  have "atom x \<sharp> (\<Delta>, z) \<or> x \<in> domA \<Delta> - set (v # L)"  using Variable.hyps(3) by (auto simp add: fresh_Pair)
  thus ?case using \<open>atom x \<sharp> v\<close> by (auto simp add: fresh_Pair fresh_Cons fresh_at_base)
next

case (Bool \<Gamma> b L)
  thus ?case by auto
next

case (IfThenElse \<Gamma> scrut L \<Delta> b e\<^sub>1 e\<^sub>2 \<Theta> z)
  from \<open>atom x \<sharp> (\<Gamma>, scrut ? e\<^sub>1 : e\<^sub>2)\<close>
  have "atom x \<sharp> (\<Gamma>, scrut)" and "atom x \<sharp> (e\<^sub>1, e\<^sub>2)" by (auto simp add: fresh_Pair)
  from IfThenElse.hyps(2)[OF this(1)]
  show ?case
  proof
    assume "atom x \<sharp> (\<Delta>, Bool b)" with \<open>atom x \<sharp> (e\<^sub>1, e\<^sub>2)\<close>
    have "atom x \<sharp> (\<Delta>, if b then e\<^sub>1 else e\<^sub>2)" by auto
    from IfThenElse.hyps(4)[OF this]
    show ?thesis.
  next
    assume "x \<in> domA \<Delta> - set L"
    with reds_doesnt_forget[OF \<open>\<Delta> : (if b then e\<^sub>1 else e\<^sub>2) \<Down>\<^bsub>L\<^esub> \<Theta> : z\<close>]
    show ?thesis by auto
  qed
next

case (Let \<Delta> \<Gamma> L body \<Theta> z)
  show ?case
  proof (cases "x \<in> domA \<Delta>")
    case False
      hence "atom x \<sharp> \<Delta>" using Let.prems by(auto simp add: fresh_Pair)      
      show ?thesis
        apply(rule Let.hyps(3))
        using Let.prems \<open>atom x \<sharp> \<Delta>\<close> False
        by (auto simp add: fresh_Pair fresh_append)
  next
    case True
      hence "x \<notin> set L"
        using Let(1)
        by (metis fresh_PairD(2) fresh_star_def image_eqI set_not_fresh)
      with True
      show ?thesis
      using reds_doesnt_forget[OF Let.hyps(2)] by auto
  qed
qed

lemma reds_fresh_fv: "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   x \<in> fv (\<Delta>, z) \<and> (x \<notin> domA \<Delta> \<or>  x \<in> set L)
  \<rbrakk> \<Longrightarrow> x \<in> fv (\<Gamma>, e)"
using reds_fresh
unfolding fv_def fresh_def
by blast

lemma new_free_vars_on_heap:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  shows "fv (\<Delta>, z) - domA \<Delta> \<subseteq> fv (\<Gamma>, e) - domA \<Gamma>"
using reds_fresh_fv[OF assms(1)] reds_doesnt_forget[OF assms(1)] by auto

lemma reds_pres_closed:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  and     "fv (\<Gamma>, e) \<subseteq> set L \<union> domA \<Gamma>"
  shows   "fv (\<Delta>, z) \<subseteq> set L \<union> domA \<Delta>"
using new_free_vars_on_heap[OF assms(1)] assms(2) by auto

text \<open>
Reducing the set of variables to avoid is always possible.
\<close> 

lemma reds_smaller_L: "\<lbrakk> \<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z;
   set L' \<subseteq> set L
  \<rbrakk> \<Longrightarrow> \<Gamma> : e \<Down>\<^bsub>L'\<^esub> \<Delta> : z"
proof(nominal_induct avoiding : L' rule: reds.strong_induct)
case (Lambda \<Gamma> x e L L')
  show ?case
    by (rule reds.Lambda)
next
case (Application y \<Gamma> e xa L \<Delta> \<Theta> z e' L')
  from Application.hyps(10)[OF Application.prems] Application.hyps(12)[OF Application.prems]
  show ?case
    by (rule reds_ApplicationI)
next 
case (Variable \<Gamma> xa e L \<Delta> z L')
  have "set (xa # L') \<subseteq> set (xa # L)"
    using Variable.prems by auto
  thus ?case
    by (rule reds.Variable[OF Variable(1) Variable.hyps(3)])
next
case (Bool b)
  show ?case..
next
case (IfThenElse \<Gamma> scrut L \<Delta> b e\<^sub>1 e\<^sub>2 \<Theta> z L')
  thus ?case by (metis  reds.IfThenElse)
next
case (Let \<Delta> \<Gamma>  L body \<Theta> z L')
  have "atom ` domA \<Delta> \<sharp>* (\<Gamma>, L')"
    using Let(1-3) Let.prems
    by (auto simp add: fresh_star_Pair  fresh_star_set_subset)
  thus ?case
    by (rule reds.Let[OF _ Let.hyps(4)[OF Let.prems]])
qed

text \<open>Things are evaluated to a lambda expression, and the variable can be freely chose.\<close>

lemma result_evaluated:
  "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z \<Longrightarrow> isVal z"
by (induct \<Gamma> e L \<Delta> z rule:reds.induct) (auto dest: reds_doesnt_forget)


lemma result_evaluated_fresh:
  assumes "\<Gamma> : e \<Down>\<^bsub>L\<^esub> \<Delta> : z"
  obtains y e'
  where "z = (Lam [y]. e')" and "atom y \<sharp> (c::'a::fs)" | b where "z = Bool b"
proof-
  from assms
  have "isVal z" by (rule result_evaluated)
  hence "(\<exists> y e'. z = Lam [y]. e' \<and> atom y \<sharp> c) \<or> (\<exists> b. z = Bool b)"
    by (nominal_induct z avoiding: c rule:exp_strong_induct) auto
  thus thesis using that by blast
qed

end
