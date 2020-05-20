section "Formula"

theory Formula
imports Base
begin

subsection "Variables"

datatype vbl = X nat
  \<comment> \<open>FIXME there's a lot of stuff about this datatype that is
  really just a lifting from nat (what else could it be). Makes me
  wonder whether things wouldn't be clearer is we just identified vbls
  with nats\<close>

primrec deX :: "vbl => nat" where "deX (X n) = n"

lemma X_deX[simp]: "X (deX a) = a"
  by(cases a) simp

definition "zeroX = X 0"


primrec
  nextX :: "vbl => vbl" where
  "nextX (X n) = X (Suc n)"

definition
  vblcase :: "['a,vbl => 'a,vbl] => 'a" where
  "vblcase a f n = (@z. (n=zeroX \<longrightarrow> z=a) \<and> (!x. n=nextX x \<longrightarrow> z=f(x)))"

declare [[case_translation vblcase zeroX nextX]]

definition
  freshVar :: "vbl set => vbl" where
  "freshVar vs = X (LEAST n. n \<notin> deX ` vs)"
    
lemma nextX_nextX[iff]: "nextX x = nextX y = (x =  y)"
  by(cases x, cases y) auto

lemma inj_nextX: "inj nextX"
  by(auto simp add: inj_on_def)

lemma ind': "P zeroX ==> (! v . P v --> P (nextX v)) ==> P v'"
  apply (case_tac v', simp)
  apply(rename_tac nat)
  apply(induct_tac nat)
   apply(simp add: zeroX_def)
  apply(rename_tac n)
  apply (drule_tac x="X n" in spec, simp)
  done

lemma ind: "\<lbrakk> P zeroX; \<And> v. P v \<Longrightarrow> P (nextX v) \<rbrakk> \<Longrightarrow> P v'"
  apply(rule ind') by auto

lemma zeroX_nextX[iff]: "zeroX ~= nextX a" \<comment> \<open>FIXME iff?\<close>
  apply(case_tac a)
  apply(simp add: zeroX_def)
  done

lemmas nextX_zeroX[iff] = not_sym[OF zeroX_nextX]

lemma nextX: "nextX (X n) = X (Suc n)"
  apply simp done

lemma vblcase_zeroX[simp]: "vblcase a b zeroX = a" 
  by(simp add: vblcase_def)

lemma vblcase_nextX[simp]: "vblcase a b (nextX n) = b n" 
  by(simp add: vblcase_def)

lemma vbl_cases: "x = zeroX | (? y . x = nextX y)"
  apply(case_tac x, rename_tac m)
  apply(case_tac m)
  apply(simp add: zeroX_def)
  apply(rule disjI2)
  apply (rule_tac x="X nat" in exI, simp)
  done

lemma vbl_casesE: "\<lbrakk> x = zeroX \<Longrightarrow> P; \<And> y. x = nextX y \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply(auto intro: vbl_cases[elim_format]) done

lemma comp_vblcase: "f o vblcase a b = vblcase (f a) (f o b)"
  apply(rule ext) 
  apply(rule_tac x = x in vbl_casesE) 
   apply(simp_all add: vblcase_zeroX vblcase_nextX) 
  done

lemma equalOn_vblcaseI': "equalOn (preImage nextX A) f g ==> equalOn A (vblcase x f) (vblcase x g)"
  apply(simp add: equalOn_def) 
  apply(rule+)
  apply (case_tac xa rule: vbl_casesE, simp, simp)
  apply(drule_tac x=y in bspec)
  apply(simp add: preImage_def) 
  by assumption
    
lemma equalOn_vblcaseI: "(zeroX : A --> x=y) ==> equalOn (preImage nextX A) f g ==> equalOn A (vblcase x f) (vblcase y g)"
  apply (rule equalOnI, rule)
  apply (case_tac xa rule: vbl_casesE, simp, simp)
  apply(simp add: preImage_def equalOn_def) 
  done

lemma X_deX_connection: "X n : A = (n : (deX ` A))"
  by force

lemma finiteFreshVar: "finite A ==> freshVar A ~: A"
  apply(simp add: freshVar_def)
  apply(simp add: X_deX_connection)
  apply(rule_tac LeastI_ex)
  apply(rule_tac x="(Suc (Max (deX ` A)))" in exI)
  apply(rule natset_finite_max)
  by force

lemma freshVarI: "[| finite A; B <= A |] ==> freshVar A ~: B"
  apply(auto dest!: finiteFreshVar) done

lemma freshVarI2: "finite A ==> !x . x ~: A --> P x ==> P (freshVar A)"
  apply(auto dest!: finiteFreshVar) done

lemmas vblsimps = vblcase_zeroX vblcase_nextX zeroX_nextX
  nextX_zeroX nextX_nextX comp_vblcase


subsection "Predicates"

datatype predicate = Predicate nat

datatype signs = Pos | Neg

lemma signsE: "\<lbrakk> signs = Neg \<Longrightarrow> P; signs = Pos \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply(cases signs, auto) done

lemma expand_case_signs: "Q(case_signs vpos vneg F) = ( 
  (F = Pos --> Q (vpos)) & 
  (F = Neg --> Q (vneg)) 
 )"
  by(induct F) simp_all

primrec sign :: "signs \<Rightarrow> bool \<Rightarrow> bool"
where
  "sign Pos x = x"
| "sign Neg x = (\<not> x)"

lemma sign_arg_cong: "x = y ==> sign z x = sign z y" by simp
    
primrec invSign :: "signs \<Rightarrow> signs"
where
  "invSign Pos = Neg"
| "invSign Neg = Pos"


subsection "Formulas"

datatype formula =
    FAtom signs predicate "(vbl list)"
  | FConj signs formula formula
  | FAll  signs formula  


subsection "formula signs induct, formula signs cases"

lemma formula_signs_induct: "[|
  ! p vs. P (FAtom Pos p vs);
  ! p vs. P (FAtom Neg p vs);
  !! A B  . [| P A; P B |] ==> P (FConj Pos A B);
  !! A B  . [| P A; P B |] ==> P (FConj Neg A B);
  !! A    . [| P A |] ==> P (FAll  Pos A); 
  !! A    . [| P A |] ==> P (FAll  Neg A) 
  |]
  ==> P A"
  apply(induct_tac A) 
  apply(rule signs.induct, force, force)+
  done

lemma formula_signs_cases: "!!P. 
  [| !! p vs . P (FAtom Pos p vs); 
  !! p vs . P (FAtom Neg p vs); 
  !! f1 f2  . P (FConj Pos f1 f2); 
  !! f1 f2  . P (FConj Neg f1 f2); 
  !! f1    . P (FAll  Pos f1); 
  !! f1    . P (FAll  Neg f1) |] 
  ==> P A"
  apply(induct_tac A)
  apply(rule signs.induct, force, force)+
  done

    \<comment> \<open>induction using nat induction, not wellfounded induction\<close>
lemma strong_formula_induct': "!A. (! B. size B < size A --> P B) --> P A ==> ! A. size A = n --> P (A::formula)"
  by (induct_tac n rule: nat_less_induct, blast) 

lemma strong_formula_induct: "(! A. (! B. size B < size A --> P B) --> P A) ==> P (A::formula)"
 by (rule strong_formula_induct'[rule_format], blast+) 

lemma sizelemmas: "size A < size (FConj z A B)"
  "size B < size (FConj z A B)"
  "size A < size (FAll  z A)"
  by auto

lemma expand_case_formula:
  "Q(case_formula fatom fconj fall F) = ( 
  (! z P vs  . F = FAtom z P vs  --> Q (fatom z P vs)) & 
  (! z A0 A1 . F = FConj z A0 A1 --> Q (fconj z A0 A1)) & 
  (! z A     . F = FAll  z A     --> Q (fall  z A)) 
 )"
  apply(cases F) apply simp_all done

primrec FNot :: "formula => formula"
where
  FNot_FAtom: "FNot (FAtom z P vs)  = FAtom (invSign z) P vs"
| FNot_FConj: "FNot (FConj z A0 A1) = FConj (invSign z) (FNot A0) (FNot A1)"    
| FNot_FAll:  "FNot (FAll  z body)  = FAll  (invSign z) (FNot body)"

primrec neg  :: "signs => signs"
where
  "neg Pos = Neg"
| "neg Neg = Pos"

primrec
  dual :: "[(signs => signs),(signs => signs),(signs => signs)] => formula => formula"
where
  dual_FAtom: "dual p q r (FAtom z P vs)  = FAtom (p z) P vs"
| dual_FConj: "dual p q r (FConj z A0 A1) = FConj (q z) (dual p q r A0) (dual p q r A1)"
| dual_FAll:  "dual p q r (FAll  z body)  = FAll  (r z) (dual p q r body)"

lemma dualCompose: "dual p q r o dual P Q R = dual (p o P) (q o Q) (r o R)"
  apply(rule ext)
  apply (induct_tac x, auto) 
  done

lemma dualFNot': "dual invSign invSign invSign = FNot"
  apply(rule ext) 
  apply(induct_tac x) 
  apply auto
  done

lemma dualFNot: "dual invSign id id (FNot A) = FNot (dual invSign id id A)"
  by(induct A) (auto simp: id_def)

lemma dualId: "dual id id id A = A"
  by(induct A) (auto simp: id_def)


subsection "Frees"

primrec freeVarsF  :: "formula => vbl set"
where
  freeVarsFAtom: "freeVarsF (FAtom z P vs)  = set vs"
| freeVarsFConj: "freeVarsF (FConj z A0 A1) = (freeVarsF A0) Un (freeVarsF A1)"    
| freeVarsFAll:  "freeVarsF (FAll  z body)  = preImage nextX (freeVarsF body)"

definition
  freeVarsFL :: "formula list => vbl set" where
  "freeVarsFL gamma = Union (freeVarsF ` (set gamma))"

lemma freeVarsF_FNot[simp]: "freeVarsF (FNot A) = freeVarsF A"
  by(induct A) auto

lemma finite_freeVarsF[simp]: "finite (freeVarsF A)"
  by(induct A) (auto simp add: inj_nextX finite_preImage) 

lemma freeVarsFL_nil[simp]: "freeVarsFL ([]) = {}"
  by(simp add: freeVarsFL_def)

lemma freeVarsFL_cons: "freeVarsFL (A#Gamma) = freeVarsF A \<union> freeVarsFL Gamma"
  by(simp add: freeVarsFL_def)
    \<comment> \<open>FIXME not simp, since simp stops some later lemmas because the simpset isn't confluent\<close>

lemma finite_freeVarsFL[simp]: "finite (freeVarsFL gamma)"
  by(induct gamma) (auto simp: freeVarsFL_cons)

lemma freeVarsDual: "freeVarsF (dual p q r A) = freeVarsF A"
  by(induct A) auto


subsection "Substitutions"

primrec subF :: "[vbl => vbl,formula] => formula"
where
  subFAtom: "subF theta (FAtom z P vs)  = FAtom z P (map theta vs)"
| subFConj: "subF theta (FConj z A0 A1) = FConj z (subF theta A0) (subF theta A1)"
| subFAll: "subF theta (FAll z body)  = 
  FAll  z (subF (% v . (case v of zeroX => zeroX | nextX v => nextX (theta v))) body)"

lemma size_subF: "!!theta. size (subF theta A) = size (A::formula)"
  by(induct A) auto

lemma subFNot: "!!theta. subF theta (FNot A) = FNot (subF theta A)"
  by(induct A) auto

lemma subFDual: "!!theta. subF theta (dual p q r A) = dual p q r (subF theta A)"
  by(induct A) auto

definition
  instanceF :: "[vbl,formula] => formula" where
  "instanceF w body = subF (%v. case v of zeroX => w | nextX v => v) body"

lemma size_instance: "!!v. size (instanceF v A) = size (A::formula)"
  by(induct A) (auto simp: instanceF_def size_subF)

lemma instanceFDual: "instanceF u (dual p q r A) = dual p q r (instanceF u A)" 
  by(induct A) (simp_all add: instanceF_def subFDual)


subsection "Models"

typedecl
  object

axiomatization obj :: "nat => object"
where inj_obj: "inj obj"


subsection "model, non empty set and positive atom valuation"

definition "model = {z :: (object set * ([predicate,object list] => bool)). (fst z ~= {})}"

typedef model = model
  unfolding model_def by auto

definition
  objects :: "model => object set" where
  "objects M = fst (Rep_model M)"

definition
  evalP :: "model => predicate => object list => bool" where
  "evalP M = snd (Rep_model M)"


lemma evalP_arg2_cong: "x = y ==> evalP M p x = evalP M p y" by simp

lemma objectsNonEmpty: "objects M \<noteq> {}"
  using Rep_model[of M]
  by(simp add: objects_def model_def)

lemma modelsNonEmptyI: "fst (Rep_model M) \<noteq> {}"
  using Rep_model[of M] by(simp add: objects_def model_def)


subsection "Validity"

primrec evalF :: "[model,vbl => object,formula] => bool"
where
  evalFAtom: "evalF M phi (FAtom z P vs)  = sign z (evalP M P (map phi vs))"
| evalFConj: "evalF M phi (FConj z A0 A1) = sign z (sign z (evalF M phi A0) & sign z (evalF M phi A1))"
| evalFAll:  "evalF M phi (FAll  z body)  = sign z (!x: (objects M).
                                                       sign z
                                                            (evalF M (%v . (case v of
                                                                                zeroX   => x
                                                                              | nextX v => phi v)) body))"

definition
  valid :: "formula => bool" where
  "valid F \<longleftrightarrow> (\<forall>M phi. evalF M phi F = True)"


lemma evalF_FAll: "evalF M phi (FAll Pos A) = (!x: (objects M). (evalF M (vblcase x (%v .phi v)) A))"
  by simp
  
lemma evalF_FEx: "evalF M phi (FAll Neg A) = ( ? x:(objects M). (evalF M (vblcase x (%v. phi v)) A))"
  by simp

lemma evalF_arg2_cong: "x = y ==> evalF M p x = evalF M p y" by simp

lemma evalF_FNot: "!!phi. evalF M phi (FNot A) = (\<not> evalF M phi A)"
  by(induct A rule: formula_signs_induct) simp_all

lemma evalF_equiv[rule_format]: "! f g. (equalOn (freeVarsF A) f g) \<longrightarrow> (evalF M f A = evalF M g A)"
  apply(induct A)
    apply (force simp:equalOn_def cong: map_cong, clarify) apply simp apply(drule_tac equalOn_UnD) apply force
  apply clarify apply simp apply(rename_tac signs A f g) apply(rule_tac f = "sign signs" in arg_cong) apply(rule ball_cong) apply rule 
  apply(rule_tac f = "sign signs" in arg_cong) apply(force intro: equalOn_vblcaseI')
  done
    \<comment> \<open>FIXME tricky to automate cong args convincingly?\<close>

    \<comment> \<open>composition of substitutions\<close>
lemma evalF_subF_eq: "!phi theta. evalF M phi (subF theta A) = evalF M (phi o theta) A"
  apply(induct_tac A)
    apply(simp del: o_apply)
   apply(simp del: o_apply)
  apply(intro allI)
  apply(simp del: o_apply)
  apply(rename_tac signs phi0 phi theta)
  apply(rule_tac f="sign signs" in arg_cong) 
  apply(rule ball_cong) apply rule
  apply(rule_tac f="sign signs" in arg_cong)
  apply(subgoal_tac "(vblcase x phi \<circ> vblcase zeroX (\<lambda>v. nextX (theta v))) = (vblcase x (phi \<circ> theta))")
  apply(simp del: o_apply)
  apply(rule ext)
  apply (case_tac xa rule: vbl_casesE, simp, simp)
  done

lemma o_id'[simp]: "f o (% x. x) = f"
by (fold id_def, simp)

lemma evalF_instance: "evalF M phi (instanceF u A) = evalF M (vblcase (phi u) phi) A"
  apply(simp add: instanceF_def evalF_subF_eq vblsimps)
  done

\<comment> \<open>FIXME move\<close>

lemma s[simp]:" FConj signs formula1 formula2 \<noteq> formula1"
  apply(induct_tac formula1, auto) done

lemma s'[simp]:" FConj signs formula1 formula2 \<noteq> formula2" 
  apply(induct formula2, auto) done

lemma instanceF_E: "instanceF g formula \<noteq> FAll signs formula"
  apply clarify
  apply(subgoal_tac "Suc (size (instanceF g formula)) = (size (FAll signs formula))")
  apply force
  apply(simp (no_asm) only: size_instance[rule_format])
  apply simp done

end
