(*
Title: WHATandWHERE-Security
Authors: Sylvia Grewe, Alexander Lux, Heiko Mantel, Jens Sauer
*)
theory Type_System_example
imports Type_System Strong_Security.Expr Strong_Security.Domain_example
begin

\<comment> \<open>When interpreting, we have to instantiate the type for domains. As an example, we take a type containing 'low' and 'high' as domains.\<close>

consts DA :: "('id,Dom) DomainAssignment"
consts BMap :: "'val \<Rightarrow> bool"
consts lH :: "(Dom,('id,'val) Expr) lHatches"

\<comment> \<open>redefine all the abbreviations necessary for auxiliary lemmas with the 
  correct parameter instantiation\<close>

abbreviation MWLsStepsdet' :: 
  "(('id,'val) Expr, 'id, 'val, (('id,'val) Expr,'id) MWLsCom) TLSteps_curry"
("(1\<langle>_,/_\<rangle>) \<rightarrow>\<lhd>_\<rhd>/ (1\<langle>_,/_\<rangle>)" [0,0,0,0,0] 81)
where
"\<langle>c1,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>c2,m2\<rangle> \<equiv> 
  ((c1,m1),\<alpha>,(c2,m2)) \<in> MWLs_semantics.MWLsSteps_det ExprEval BMap"

abbreviation d_equal' :: "('id, 'val) State 
  \<Rightarrow> Dom \<Rightarrow> ('id, 'val) State \<Rightarrow> bool" 
( "(_ =\<^bsub>_\<^esub> _)" )
where
"m =\<^bsub>d\<^esub> m' \<equiv> WHATWHERE.d_equal DA d m m'"

abbreviation dH_equal' :: "('id, 'val) State \<Rightarrow> Dom 
  \<Rightarrow> (Dom,('id,'val) Expr) Hatches
  \<Rightarrow> ('id, 'val) State \<Rightarrow> bool"
( "(_ \<sim>\<^bsub>_,_\<^esub> _)" )
where
"m \<sim>\<^bsub>d,H\<^esub> m' \<equiv> WHATWHERE.dH_equal ExprEval DA d H m m'"

abbreviation NextMem' :: "(('id,'val) Expr, 'id) MWLsCom 
  \<Rightarrow> ('id,'val) State \<Rightarrow> ('id,'val) State"
("\<lbrakk>_\<rbrakk>'(_')")
where
"\<lbrakk>c\<rbrakk>(m) 
  \<equiv> WHATWHERE.NextMem (MWLs_semantics.MWLsSteps_det ExprEval BMap) c m"

abbreviation dH_indistinguishable' :: "('id,'val) Expr \<Rightarrow> Dom 
  \<Rightarrow> (Dom,('id,'val) Expr) Hatches \<Rightarrow> ('id,'val) Expr \<Rightarrow> bool" 
( "(_ \<equiv>\<^bsub>_,_\<^esub> _)" )
where
"e1 \<equiv>\<^bsub>d,H\<^esub> e2 
  \<equiv> WHATWHERE_Secure_Programs.dH_indistinguishable ExprEval DA d H e1 e2"

abbreviation htchLoc :: "nat \<Rightarrow> (Dom, ('id,'val) Expr) Hatches"
where 
"htchLoc \<iota> \<equiv> WHATWHERE.htchLoc lH \<iota>"


\<comment> \<open>Security typing rules for expressions\<close>
inductive 
ExprSecTyping :: "(Dom, ('id,'val) Expr) Hatches
  \<Rightarrow> ('id, 'val) Expr \<Rightarrow> Dom \<Rightarrow> bool"
("_ \<turnstile>\<^bsub>\<E>\<^esub> _ : _")
for H :: "(Dom, ('id, 'val) Expr) Hatches"
where 
Consts: "H \<turnstile>\<^bsub>\<E>\<^esub> (Const v) : d" |
Vars: "DA x = d \<Longrightarrow> H \<turnstile>\<^bsub>\<E>\<^esub> (Var x) : d" |
Hatch: "(d,e) \<in> H \<Longrightarrow> H \<turnstile>\<^bsub>\<E>\<^esub> e : d" |
Ops: "\<lbrakk> \<forall>i < length arglist. H \<turnstile>\<^bsub>\<E>\<^esub> (arglist!i) : (dl!i) \<and> (dl!i) \<le> d \<rbrakk>
  \<Longrightarrow> H \<turnstile>\<^bsub>\<E>\<^esub> (Op f arglist) : d"

\<comment> \<open>function substituting a certain expression with another expression 
  in expressions\<close>
primrec Subst :: "('id, 'val) Expr \<Rightarrow> ('id, 'val) Expr 
  \<Rightarrow> ('id, 'val) Expr \<Rightarrow> ('id, 'val) Expr"
("_<_\\_>")
and SubstL :: "('id, 'val) Expr list \<Rightarrow> ('id, 'val) Expr 
  \<Rightarrow> ('id, 'val) Expr \<Rightarrow> ('id, 'val) Expr list"
where
"(Const v)<e1\\e2> = (if e1=(Const v) then e2 else (Const v))" |
"(Var x)<e1\\e2> = (if e1=(Var x) then e2 else (Var x))" |
"(Op f arglist)<e1\\e2> = (if e1=(Op f arglist) then e2 else 
  (Op f (SubstL arglist e1 e2)))" |

"SubstL [] e1 e2 = []" |
"SubstL (e#V) e1 e2 = (e<e1\\e2>)#(SubstL V e1 e2)"


definition SubstClosure :: "'id \<Rightarrow> ('id, 'val) Expr \<Rightarrow> bool"
where
"SubstClosure x e \<equiv> \<forall>(d',e',\<iota>') \<in> lH. (d',e'<(Var x)\\e>,\<iota>') \<in> lH"

definition synAssignSC :: "'id \<Rightarrow> ('id, 'val) Expr \<Rightarrow> nat \<Rightarrow> bool"
where
"synAssignSC x e \<iota> \<equiv> \<exists>d. ((htchLoc \<iota>) \<turnstile>\<^bsub>\<E>\<^esub> e : d \<and> d \<le> DA x)
  \<and> (SubstClosure x e)"

definition synWhileSC :: "('id, 'val) Expr \<Rightarrow> bool"
where
"synWhileSC e \<equiv> (\<exists>d. ({} \<turnstile>\<^bsub>\<E>\<^esub> e : d) \<and> (\<forall>d'. d \<le> d'))"

definition synIfSC :: "('id, 'val) Expr
  \<Rightarrow> (('id, 'val) Expr, 'id) MWLsCom 
  \<Rightarrow> (('id, 'val) Expr, 'id) MWLsCom \<Rightarrow> bool" 
where
"synIfSC e c1 c2 \<equiv> \<exists>d. ({} \<turnstile>\<^bsub>\<E>\<^esub> e : d \<and> (\<forall>d'. d \<le> d'))"


\<comment> \<open>auxiliary lemma for locale interpretation (theorem 7 in original paper)\<close>
lemma ExprTypable_with_smallerd_implies_dH_indistinguishable:
  "\<lbrakk> H \<turnstile>\<^bsub>\<E>\<^esub> e : d'; d' \<le> d \<rbrakk> \<Longrightarrow> e \<equiv>\<^bsub>d,H\<^esub> e"
proof (induct rule: ExprSecTyping.induct, 
    simp_all add: WHATWHERE_Secure_Programs.dH_indistinguishable_def 
    WHATWHERE.dH_equal_def WHATWHERE.d_equal_def, auto)
  fix dl arglist f m1 m2 d' d
  assume main: "\<forall>i < length arglist.
    (H \<turnstile>\<^bsub>\<E>\<^esub> (arglist!i) : (dl!i)) \<and> (dl!i \<le> d \<longrightarrow>
    (\<forall>m1 m2. (\<forall>x. DA x \<le> d \<longrightarrow> m1 x = m2 x) \<and>
    (\<forall>(d',e)\<in>H. d' \<le> d \<longrightarrow> ExprEval e m1 = ExprEval e m2) \<longrightarrow>
    ExprEval (arglist!i) m1 = ExprEval (arglist!i) m2)) \<and> dl!i \<le> d'"
  assume smaller: "d' \<le> d"
  assume eqeval: "\<forall>(d',e) \<in> H. d' \<le> d \<longrightarrow> ExprEval e m1 = ExprEval e m2"
  assume eqstate: "\<forall>x. DA x \<le> d \<longrightarrow> m1 x = m2 x"
  
  from main smaller have irangesubst:
    "\<forall>i < length arglist. dl!i \<le> d"
    by (metis order_trans)

  with eqstate eqeval main have 
    "\<forall>i < length arglist. ExprEval (arglist!i) m1 
       = ExprEval (arglist!i) m2"
    by force

  hence substmap: "(ExprEvalL arglist m1) = (ExprEvalL arglist m2)" 
    by (induct arglist, auto, force)

  show "f (ExprEvalL arglist m1) = f (ExprEvalL arglist m2)"
    by (subst substmap, auto)

qed

\<comment> \<open>auxiliary lemma about substitutions in expressions and in memories\<close>
lemma substexp_substmem:
"ExprEval e'<Var x\\e> m = ExprEval e' (m(x := ExprEval e m))
  \<and> ExprEvalL (SubstL elist (Var x) e) m
  = ExprEvalL elist (m(x := ExprEval e m))"
by (induct_tac e' and elist rule: ExprEval.induct ExprEvalL.induct, simp_all)


\<comment> \<open>another auxiliary lemma for locale interpretation (lemma 8 in original paper)\<close>
lemma SubstClosure_implications:
"\<lbrakk> SubstClosure x e; m \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> m'; 
  \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m) =\<^bsub>d\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m') \<rbrakk>
  \<Longrightarrow> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m) \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m')"
proof -
  fix m1 m1'
  assume substclosure: "SubstClosure x e"
  assume dequalm2: "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) =\<^bsub>d\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1')"
  assume dhequalm1: "m1 \<sim>\<^bsub>d,(htchLoc \<iota>')\<^esub> m1'"  
  
  from MWLs_semantics.nextmem_exists_and_unique obtain m2 where m1step:
    "(\<exists>p \<alpha>. \<langle>x :=\<^bsub>\<iota>\<^esub> e,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2\<rangle>) 
    \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>x :=\<^bsub>\<iota>\<^esub> e,m1\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m2)"
    by force
  hence m2_is_next: "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) = m2"
    by (simp add: WHATWHERE.NextMem_def, auto)
  from m1step MWLs_semantics.MWLsSteps_det.assign
     [of "ExprEval" "e" "m1" _ "x" "\<iota>" "BMap"]
  have m2eq: "m2 = m1(x := (ExprEval e m1))"
    by auto

  from MWLs_semantics.nextmem_exists_and_unique obtain m2' where m1'step:
    "(\<exists>p \<alpha>. \<langle>x :=\<^bsub>\<iota>\<^esub> e,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m2'\<rangle>) 
    \<and> (\<forall>m''. (\<exists>p \<alpha>. \<langle>x :=\<^bsub>\<iota>\<^esub> e,m1'\<rangle> \<rightarrow>\<lhd>\<alpha>\<rhd> \<langle>p,m''\<rangle>) \<longrightarrow> m'' = m2')"
    by force
  hence m2'_is_next: "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1') = m2'"
    by (simp add: WHATWHERE.NextMem_def, auto)
  from m1'step MWLs_semantics.MWLsSteps_det.assign
     [of "ExprEval" "e" "m1'" _ "x" "\<iota>" "BMap"]
  have m2'eq: "m2' = m1'(x := (ExprEval e m1'))"
    by auto

  from m2eq substexp_substmem
  have substeval1: "\<forall>e'. ExprEval (e'<Var x\\e>) m1 = ExprEval e' m2"
    by force

  from m2'eq substexp_substmem
  have substeval2: "\<forall>e'. ExprEval e'<Var x\\e> m1' = ExprEval e' m2'"
    by force
   
  from substclosure have 
    "\<forall>(d',e') \<in> htchLoc \<iota>'. (d',e'<Var x\\e>) \<in> (htchLoc \<iota>')"
    by (simp add: SubstClosure_def WHATWHERE.htchLoc_def, auto)

  with dhequalm1 have 
    "\<forall>(d',e') \<in> htchLoc \<iota>'. 
    d' \<le> d \<longrightarrow> ExprEval e'<Var x\\e> m1 = ExprEval e'<Var x\\e> m1'"
    by (simp add: WHATWHERE.dH_equal_def, auto)

  with substeval1 substeval2 have 
    "\<forall>(d',e') \<in> htchLoc \<iota>'.
    d' \<le> d \<longrightarrow> ExprEval e' m2 = ExprEval e' m2'"
    by auto

  with dequalm2 m2_is_next m2'_is_next
  show "\<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1) \<sim>\<^bsub>d,htchLoc \<iota>'\<^esub> \<lbrakk>x :=\<^bsub>\<iota>\<^esub> e\<rbrakk>(m1')"
    by (simp add: WHATWHERE.dH_equal_def)
qed

\<comment> \<open>interpretation of the abstract type system using the above definitions for the side conditions\<close>
interpretation Type_System_example: Type_System ExprEval BMap DA lH
  synAssignSC synWhileSC synIfSC
by (unfold_locales, auto,
  metis ExprTypable_with_smallerd_implies_dH_indistinguishable 
  synAssignSC_def,
  metis SubstClosure_implications synAssignSC_def, 
  simp add: synWhileSC_def,
  metis ExprTypable_with_smallerd_implies_dH_indistinguishable 
  WHATWHERE_Secure_Programs.empH_implies_dHindistinguishable_eq_dindistinguishable, 
  simp add: synIfSC_def,
  metis ExprTypable_with_smallerd_implies_dH_indistinguishable 
  WHATWHERE_Secure_Programs.empH_implies_dHindistinguishable_eq_dindistinguishable)

end
