section \<open>More Terms and Literals\<close>

theory Resolution imports TermsAndLiterals Tree begin

fun complement :: "'t literal \<Rightarrow> 't literal" ("_\<^sup>c" [300] 300) where
  "(Pos P ts)\<^sup>c = Neg P ts"  
| "(Neg P ts)\<^sup>c = Pos P ts"

lemma cancel_comp1: "(l\<^sup>c)\<^sup>c = l" by (cases l) auto   

lemma cancel_comp2:
  assumes asm: "l\<^sub>1\<^sup>c = l\<^sub>2\<^sup>c"
  shows "l\<^sub>1 = l\<^sub>2"
proof -
  from asm have "(l\<^sub>1\<^sup>c)\<^sup>c = (l\<^sub>2\<^sup>c)\<^sup>c" by auto
  then have "l\<^sub>1 = (l\<^sub>2\<^sup>c)\<^sup>c" using cancel_comp1[of l\<^sub>1] by auto
  then show ?thesis using cancel_comp1[of l\<^sub>2] by auto
qed

lemma comp_exi1: "\<exists>l'. l' = l\<^sup>c" by (cases l) auto 

lemma comp_exi2: "\<exists>l. l' = l\<^sup>c"
proof
  show "l' = (l'\<^sup>c)\<^sup>c" using cancel_comp1[of l'] by auto
qed

lemma comp_swap: "l\<^sub>1\<^sup>c = l\<^sub>2 \<longleftrightarrow> l\<^sub>1 = l\<^sub>2\<^sup>c" 
proof -
  have "l\<^sub>1\<^sup>c = l\<^sub>2 \<longrightarrow> l\<^sub>1 = l\<^sub>2\<^sup>c" using cancel_comp1[of l\<^sub>1] by auto
  moreover
  have "l\<^sub>1 = l\<^sub>2\<^sup>c \<longrightarrow> l\<^sub>1\<^sup>c = l\<^sub>2" using cancel_comp1 by auto
  ultimately
  show ?thesis by auto
qed

lemma sign_comp: "sign l\<^sub>1 \<noteq> sign l\<^sub>2 \<and> get_pred l\<^sub>1 = get_pred l\<^sub>2 \<and> get_terms l\<^sub>1 = get_terms l\<^sub>2 \<longleftrightarrow> l\<^sub>2 = l\<^sub>1\<^sup>c"
by (cases l\<^sub>1; cases l\<^sub>2) auto

lemma sign_comp_atom: "sign l\<^sub>1 \<noteq> sign l\<^sub>2 \<and> get_atom l\<^sub>1 = get_atom l\<^sub>2 \<longleftrightarrow> l\<^sub>2 = l\<^sub>1\<^sup>c"
by (cases l\<^sub>1; cases l\<^sub>2) auto


section \<open>Clauses\<close>

type_synonym 't clause = "'t literal set"

abbreviation complementls :: "'t literal set \<Rightarrow> 't literal set" ("_\<^sup>C" [300] 300) where 
  "L\<^sup>C \<equiv> complement ` L"

lemma cancel_compls1: "(L\<^sup>C)\<^sup>C = L"
apply (auto simp add: cancel_comp1)
apply (metis imageI cancel_comp1) 
done

lemma cancel_compls2:
  assumes asm: "L\<^sub>1\<^sup>C = L\<^sub>2\<^sup>C"
  shows "L\<^sub>1 = L\<^sub>2"
proof -
  from asm have "(L\<^sub>1\<^sup>C)\<^sup>C = (L\<^sub>2\<^sup>C)\<^sup>C" by auto
  then show ?thesis using cancel_compls1[of L\<^sub>1] cancel_compls1[of L\<^sub>2] by simp
qed

fun vars\<^sub>t  :: "fterm \<Rightarrow> var_sym set" where
  "vars\<^sub>t (Var x) = {x}"
| "vars\<^sub>t (Fun f ts) = (\<Union>t \<in> set ts. vars\<^sub>t t)"

abbreviation vars\<^sub>t\<^sub>s :: "fterm list \<Rightarrow> var_sym set" where 
  "vars\<^sub>t\<^sub>s ts \<equiv> (\<Union>t \<in> set ts. vars\<^sub>t t)"

definition vars\<^sub>l :: "fterm literal \<Rightarrow> var_sym set" where 
  "vars\<^sub>l l = vars\<^sub>t\<^sub>s (get_terms l)"

definition vars\<^sub>l\<^sub>s :: "fterm literal set \<Rightarrow> var_sym set" where 
  "vars\<^sub>l\<^sub>s L \<equiv> \<Union>l\<in>L. vars\<^sub>l l"

lemma ground_vars\<^sub>t:
  assumes "ground\<^sub>t t"
  shows "vars\<^sub>t t = {}" 
using assms by (induction t) auto

lemma ground\<^sub>t\<^sub>s_vars\<^sub>t\<^sub>s: 
  assumes "ground\<^sub>t\<^sub>s ts"
  shows "vars\<^sub>t\<^sub>s ts = {}"
using assms ground_vars\<^sub>t by auto

lemma ground\<^sub>l_vars\<^sub>l:
  assumes "ground\<^sub>l l"
  shows "vars\<^sub>l l = {}" 
  unfolding vars\<^sub>l_def using assms ground_vars\<^sub>t by auto

lemma ground\<^sub>l\<^sub>s_vars\<^sub>l\<^sub>s: 
  assumes "ground\<^sub>l\<^sub>s L"
  shows "vars\<^sub>l\<^sub>s L = {}" unfolding vars\<^sub>l\<^sub>s_def using assms ground\<^sub>l_vars\<^sub>l by auto

lemma ground_comp: "ground\<^sub>l (l\<^sup>c) \<longleftrightarrow> ground\<^sub>l l" by (cases l) auto

lemma  ground_compls: "ground\<^sub>l\<^sub>s (L\<^sup>C) \<longleftrightarrow> ground\<^sub>l\<^sub>s L" using ground_comp by auto

(* Alternative - Collect variables with vars and see if empty set *)


section \<open>Semantics\<close>

type_synonym 'u fun_denot  = "fun_sym  \<Rightarrow> 'u list \<Rightarrow> 'u"
type_synonym 'u pred_denot = "pred_sym \<Rightarrow> 'u list \<Rightarrow> bool"
type_synonym 'u var_denot  = "var_sym  \<Rightarrow> 'u"

fun eval\<^sub>t  :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> fterm \<Rightarrow> 'u" where
  "eval\<^sub>t E F (Var x) = E x"
| "eval\<^sub>t E F (Fun f ts) = F f (map (eval\<^sub>t E F) ts)"

abbreviation eval\<^sub>t\<^sub>s :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> fterm list \<Rightarrow> 'u list" where
  "eval\<^sub>t\<^sub>s E F ts \<equiv> map (eval\<^sub>t E F) ts"

fun eval\<^sub>l :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "eval\<^sub>l E F G (Pos p ts) \<longleftrightarrow>  G p (eval\<^sub>t\<^sub>s E F ts)"
| "eval\<^sub>l E F G (Neg p ts) \<longleftrightarrow> \<not>G p (eval\<^sub>t\<^sub>s E F ts)"

definition eval\<^sub>c :: "'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "eval\<^sub>c F G C \<longleftrightarrow> (\<forall>E. \<exists>l \<in> C. eval\<^sub>l E F G l)"

definition eval\<^sub>c\<^sub>s :: "'u fun_denot \<Rightarrow> 'u pred_denot \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "eval\<^sub>c\<^sub>s F G Cs \<longleftrightarrow> (\<forall>C \<in> Cs. eval\<^sub>c F G C)"


subsection \<open>Semantics of Ground Terms\<close>

lemma ground_var_denott: 
  assumes "ground\<^sub>t t"
  shows "eval\<^sub>t E F t = eval\<^sub>t E' F t"
using assms proof (induction t)
  case (Var x)
  then have "False" by auto
  then show ?case by auto
next
  case (Fun f ts)
  then have "\<forall>t \<in> set ts. ground\<^sub>t t" by auto 
  then have "\<forall>t \<in> set ts. eval\<^sub>t E F t = eval\<^sub>t E' F t" using Fun by auto
  then have "eval\<^sub>t\<^sub>s E F ts = eval\<^sub>t\<^sub>s E' F ts" by auto
  then have "F f (map (eval\<^sub>t E F) ts) = F f (map (eval\<^sub>t E' F) ts)" by metis
  then show ?case by simp
qed

lemma ground_var_denotts: 
  assumes "ground\<^sub>t\<^sub>s ts"
  shows "eval\<^sub>t\<^sub>s E F ts = eval\<^sub>t\<^sub>s E' F ts"
  using assms ground_var_denott by (metis map_eq_conv)


lemma ground_var_denot: 
  assumes "ground\<^sub>l l"
  shows "eval\<^sub>l E F G l = eval\<^sub>l E' F G l"
using assms proof (induction l)
  case Pos then show ?case using ground_var_denotts by (metis eval\<^sub>l.simps(1) literal.sel(3))
next
  case Neg then show ?case using ground_var_denotts by (metis eval\<^sub>l.simps(2) literal.sel(4))
qed


section \<open>Substitutions\<close>

type_synonym substitution = "var_sym \<Rightarrow> fterm" 

fun sub  :: "fterm \<Rightarrow> substitution \<Rightarrow> fterm" (infixl "\<cdot>\<^sub>t" 55) where
  "(Var x) \<cdot>\<^sub>t \<sigma> = \<sigma> x"
| "(Fun f ts) \<cdot>\<^sub>t \<sigma> = Fun f (map (\<lambda>t. t \<cdot>\<^sub>t \<sigma>) ts)"

abbreviation subs :: "fterm list \<Rightarrow> substitution \<Rightarrow> fterm list" (infixl "\<cdot>\<^sub>t\<^sub>s" 55) where
  "ts \<cdot>\<^sub>t\<^sub>s \<sigma> \<equiv> (map (\<lambda>t. t \<cdot>\<^sub>t \<sigma>) ts)"

fun subl :: "fterm literal \<Rightarrow> substitution \<Rightarrow> fterm literal" (infixl "\<cdot>\<^sub>l" 55) where
  "(Pos p ts) \<cdot>\<^sub>l \<sigma> = Pos p (ts \<cdot>\<^sub>t\<^sub>s \<sigma>)"
| "(Neg p ts) \<cdot>\<^sub>l \<sigma> = Neg p (ts \<cdot>\<^sub>t\<^sub>s \<sigma>)"

abbreviation subls :: "fterm literal set \<Rightarrow> substitution \<Rightarrow> fterm literal set" (infixl "\<cdot>\<^sub>l\<^sub>s" 55) where
  "L \<cdot>\<^sub>l\<^sub>s \<sigma> \<equiv> (\<lambda>l. l \<cdot>\<^sub>l \<sigma>) ` L"

lemma subls_def2: "L \<cdot>\<^sub>l\<^sub>s \<sigma> = {l \<cdot>\<^sub>l \<sigma>|l. l \<in> L}" by auto

definition instance_of\<^sub>t :: "fterm \<Rightarrow> fterm \<Rightarrow> bool" where
  "instance_of\<^sub>t t\<^sub>1 t\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. t\<^sub>1 = t\<^sub>2 \<cdot>\<^sub>t \<sigma>)"

definition instance_of\<^sub>t\<^sub>s :: "fterm list \<Rightarrow> fterm list \<Rightarrow> bool" where
  "instance_of\<^sub>t\<^sub>s ts\<^sub>1 ts\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. ts\<^sub>1 = ts\<^sub>2 \<cdot>\<^sub>t\<^sub>s \<sigma>)"

definition instance_of\<^sub>l :: "fterm literal \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "instance_of\<^sub>l l\<^sub>1 l\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. l\<^sub>1 = l\<^sub>2 \<cdot>\<^sub>l \<sigma>)"

definition instance_of\<^sub>l\<^sub>s :: "fterm clause \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "instance_of\<^sub>l\<^sub>s C\<^sub>1 C\<^sub>2 \<longleftrightarrow> (\<exists>\<sigma>. C\<^sub>1 = C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>)"

lemma comp_sub: "(l\<^sup>c) \<cdot>\<^sub>l \<sigma>=(l \<cdot>\<^sub>l \<sigma>)\<^sup>c" 
by (cases l) auto

lemma compls_subls: "(L\<^sup>C) \<cdot>\<^sub>l\<^sub>s \<sigma>=(L \<cdot>\<^sub>l\<^sub>s \<sigma>)\<^sup>C" 
using comp_sub apply auto
apply (metis image_eqI)
done

lemma subls_union: "(L\<^sub>1 \<union> L\<^sub>2) \<cdot>\<^sub>l\<^sub>s \<sigma> = (L\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>) \<union> (L\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>)" by auto

(* 
  Alternative: apply a substitution that is a bijection between the set of variables in C1 and some other set.
 *)
definition var_renaming_of :: "fterm clause \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "var_renaming_of C\<^sub>1 C\<^sub>2 \<longleftrightarrow> instance_of\<^sub>l\<^sub>s C\<^sub>1 C\<^sub>2 \<and> instance_of\<^sub>l\<^sub>s C\<^sub>2 C\<^sub>1"


subsection \<open>The Empty Substitution\<close>

abbreviation \<epsilon> :: "substitution" where
  "\<epsilon> \<equiv> Var"

lemma empty_subt: "(t :: fterm) \<cdot>\<^sub>t \<epsilon> = t" 
by (induction t) (auto simp add: map_idI)

lemma empty_subts: "ts \<cdot>\<^sub>t\<^sub>s \<epsilon> = ts" 
using empty_subt by auto

lemma empty_subl: "l \<cdot>\<^sub>l \<epsilon> = l" 
using empty_subts by (cases l) auto

lemma empty_subls: "L \<cdot>\<^sub>l\<^sub>s \<epsilon> = L" 
using empty_subl by auto

lemma instance_of\<^sub>t_self: "instance_of\<^sub>t t t"
unfolding instance_of\<^sub>t_def
proof 
  show "t = t \<cdot>\<^sub>t \<epsilon>" using empty_subt by auto
qed

lemma instance_of\<^sub>t\<^sub>s_self: "instance_of\<^sub>t\<^sub>s ts ts"
unfolding instance_of\<^sub>t\<^sub>s_def
proof 
  show "ts = ts \<cdot>\<^sub>t\<^sub>s \<epsilon>" using empty_subts by auto
qed

lemma instance_of\<^sub>l_self: "instance_of\<^sub>l l l"
unfolding instance_of\<^sub>l_def
proof 
  show "l = l \<cdot>\<^sub>l \<epsilon>" using empty_subl by auto
qed

lemma instance_of\<^sub>l\<^sub>s_self: "instance_of\<^sub>l\<^sub>s L L"
unfolding instance_of\<^sub>l\<^sub>s_def
proof
  show "L = L \<cdot>\<^sub>l\<^sub>s \<epsilon>" using empty_subls by auto
qed


subsection \<open>Substitutions and Ground Terms\<close>

lemma ground_sub: 
  assumes "ground\<^sub>t t"
  shows "t \<cdot>\<^sub>t \<sigma> = t"
using assms by (induction t) (auto simp add: map_idI)

lemma ground_subs: 
  assumes "ground\<^sub>t\<^sub>s ts "
  shows " ts \<cdot>\<^sub>t\<^sub>s \<sigma> = ts" 
using assms ground_sub by (simp add: map_idI)

lemma ground\<^sub>l_subs: 
  assumes "ground\<^sub>l l "
  shows " l \<cdot>\<^sub>l \<sigma> = l" 
using assms ground_subs by (cases l) auto

lemma ground\<^sub>l\<^sub>s_subls:
  assumes ground: "ground\<^sub>l\<^sub>s L"
  shows "L \<cdot>\<^sub>l\<^sub>s \<sigma> = L"
proof -
  {
    fix l
    assume l_L: "l \<in> L"
    then have "ground\<^sub>l l" using ground by auto
    then have "l = l \<cdot>\<^sub>l \<sigma>" using ground\<^sub>l_subs by auto
    moreover
    then have "l \<cdot>\<^sub>l \<sigma> \<in> L \<cdot>\<^sub>l\<^sub>s \<sigma>" using l_L by auto
    ultimately
    have "l \<in> L \<cdot>\<^sub>l\<^sub>s \<sigma>" by auto
  }
  moreover
  {
    fix l
    assume l_L: "l \<in> L \<cdot>\<^sub>l\<^sub>s \<sigma>"
    then obtain l' where l'_p: "l' \<in> L \<and> l' \<cdot>\<^sub>l \<sigma> = l" by auto
    then have "l' = l" using ground ground\<^sub>l_subs by auto
    from l_L l'_p this have "l \<in> L" by auto
  } 
  ultimately show ?thesis by auto
qed


subsection \<open>Composition\<close>

definition composition :: "substitution \<Rightarrow> substitution \<Rightarrow> substitution"  (infixl "\<cdot>" 55) where
  "(\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) x = (\<sigma>\<^sub>1 x) \<cdot>\<^sub>t \<sigma>\<^sub>2"

lemma composition_conseq2t:  "(t \<cdot>\<^sub>t \<sigma>\<^sub>1) \<cdot>\<^sub>t \<sigma>\<^sub>2 = t \<cdot>\<^sub>t (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2)" 
proof (induction t)
  case (Var x) 
  have "((Var x) \<cdot>\<^sub>t \<sigma>\<^sub>1) \<cdot>\<^sub>t \<sigma>\<^sub>2 = (\<sigma>\<^sub>1 x) \<cdot>\<^sub>t \<sigma>\<^sub>2" by simp
  also have " ... = (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) x" unfolding composition_def by simp
  finally show ?case by auto
next
  case (Fun t ts)
  then show ?case unfolding composition_def by auto
qed

lemma composition_conseq2ts: "(ts \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>1) \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>2 = ts \<cdot>\<^sub>t\<^sub>s (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2)"
  using composition_conseq2t by auto

lemma composition_conseq2l: "(l \<cdot>\<^sub>l \<sigma>\<^sub>1) \<cdot>\<^sub>l \<sigma>\<^sub>2 = l \<cdot>\<^sub>l (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2)" 
  using composition_conseq2t by (cases l) auto 

lemma composition_conseq2ls: "(L \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>1) \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>2 = L \<cdot>\<^sub>l\<^sub>s (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2)" 
using composition_conseq2l apply auto
apply (metis imageI) 
done
  

lemma composition_assoc: "\<sigma>\<^sub>1 \<cdot> (\<sigma>\<^sub>2 \<cdot> \<sigma>\<^sub>3) = (\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) \<cdot> \<sigma>\<^sub>3" 
proof
  fix x
  show "(\<sigma>\<^sub>1 \<cdot> (\<sigma>\<^sub>2 \<cdot> \<sigma>\<^sub>3)) x = ((\<sigma>\<^sub>1 \<cdot> \<sigma>\<^sub>2) \<cdot> \<sigma>\<^sub>3) x"
    by (simp only: composition_def composition_conseq2t)
qed

lemma empty_comp1: "(\<sigma> \<cdot> \<epsilon>) = \<sigma>" 
proof
  fix x
  show "(\<sigma> \<cdot> \<epsilon>) x = \<sigma> x" unfolding composition_def using empty_subt by auto 
qed

lemma empty_comp2: "(\<epsilon> \<cdot> \<sigma>) = \<sigma>" 
proof
  fix x
  show "(\<epsilon> \<cdot> \<sigma>) x = \<sigma> x" unfolding composition_def by simp
qed

lemma instance_of\<^sub>t_trans : 
  assumes t\<^sub>1\<^sub>2: "instance_of\<^sub>t t\<^sub>1 t\<^sub>2"
  assumes t\<^sub>2\<^sub>3: "instance_of\<^sub>t t\<^sub>2 t\<^sub>3"
  shows "instance_of\<^sub>t t\<^sub>1 t\<^sub>3"
proof -
  from t\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "t\<^sub>1 = t\<^sub>2 \<cdot>\<^sub>t \<sigma>\<^sub>1\<^sub>2" 
    unfolding instance_of\<^sub>t_def by auto
  moreover
  from t\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "t\<^sub>2 = t\<^sub>3 \<cdot>\<^sub>t \<sigma>\<^sub>2\<^sub>3" 
    unfolding instance_of\<^sub>t_def by auto
  ultimately
  have "t\<^sub>1 = (t\<^sub>3 \<cdot>\<^sub>t \<sigma>\<^sub>2\<^sub>3) \<cdot>\<^sub>t \<sigma>\<^sub>1\<^sub>2" by auto
  then have "t\<^sub>1 = t\<^sub>3 \<cdot>\<^sub>t (\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2)" using composition_conseq2t by simp
  then show ?thesis unfolding instance_of\<^sub>t_def by auto
qed

lemma instance_of\<^sub>t\<^sub>s_trans : 
  assumes ts\<^sub>1\<^sub>2: "instance_of\<^sub>t\<^sub>s ts\<^sub>1 ts\<^sub>2"
  assumes ts\<^sub>2\<^sub>3: "instance_of\<^sub>t\<^sub>s ts\<^sub>2 ts\<^sub>3"
  shows "instance_of\<^sub>t\<^sub>s ts\<^sub>1 ts\<^sub>3"
proof -
  from ts\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "ts\<^sub>1 = ts\<^sub>2 \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>1\<^sub>2" 
    unfolding instance_of\<^sub>t\<^sub>s_def by auto
  moreover
  from ts\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "ts\<^sub>2 = ts\<^sub>3 \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>2\<^sub>3" 
    unfolding instance_of\<^sub>t\<^sub>s_def by auto
  ultimately
  have "ts\<^sub>1 = (ts\<^sub>3 \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>2\<^sub>3) \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>1\<^sub>2" by auto
  then have "ts\<^sub>1 = ts\<^sub>3 \<cdot>\<^sub>t\<^sub>s (\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2)" using composition_conseq2ts by simp
  then show ?thesis unfolding instance_of\<^sub>t\<^sub>s_def by auto
qed

lemma instance_of\<^sub>l_trans : 
  assumes l\<^sub>1\<^sub>2: "instance_of\<^sub>l l\<^sub>1 l\<^sub>2"
  assumes l\<^sub>2\<^sub>3: "instance_of\<^sub>l l\<^sub>2 l\<^sub>3"
  shows "instance_of\<^sub>l l\<^sub>1 l\<^sub>3"
proof -
  from l\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "l\<^sub>1 = l\<^sub>2 \<cdot>\<^sub>l \<sigma>\<^sub>1\<^sub>2" 
    unfolding instance_of\<^sub>l_def by auto
  moreover
  from l\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "l\<^sub>2 = l\<^sub>3 \<cdot>\<^sub>l \<sigma>\<^sub>2\<^sub>3" 
    unfolding instance_of\<^sub>l_def by auto
  ultimately
  have "l\<^sub>1 = (l\<^sub>3 \<cdot>\<^sub>l \<sigma>\<^sub>2\<^sub>3) \<cdot>\<^sub>l \<sigma>\<^sub>1\<^sub>2" by auto
  then have "l\<^sub>1 = l\<^sub>3 \<cdot>\<^sub>l (\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2)" using composition_conseq2l by simp
  then show ?thesis unfolding instance_of\<^sub>l_def by auto
qed

lemma instance_of\<^sub>l\<^sub>s_trans : 
  assumes L\<^sub>1\<^sub>2: "instance_of\<^sub>l\<^sub>s L\<^sub>1 L\<^sub>2"
  assumes L\<^sub>2\<^sub>3: "instance_of\<^sub>l\<^sub>s L\<^sub>2 L\<^sub>3"
  shows "instance_of\<^sub>l\<^sub>s L\<^sub>1 L\<^sub>3"
proof -
  from L\<^sub>1\<^sub>2 obtain \<sigma>\<^sub>1\<^sub>2 where "L\<^sub>1 = L\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>1\<^sub>2" 
    unfolding instance_of\<^sub>l\<^sub>s_def by auto
  moreover
  from L\<^sub>2\<^sub>3 obtain \<sigma>\<^sub>2\<^sub>3 where "L\<^sub>2 = L\<^sub>3 \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>2\<^sub>3" 
    unfolding instance_of\<^sub>l\<^sub>s_def by auto
  ultimately
  have "L\<^sub>1 = (L\<^sub>3 \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>2\<^sub>3) \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>1\<^sub>2" by auto
  then have "L\<^sub>1 = L\<^sub>3 \<cdot>\<^sub>l\<^sub>s (\<sigma>\<^sub>2\<^sub>3 \<cdot> \<sigma>\<^sub>1\<^sub>2)" using composition_conseq2ls by simp
  then show ?thesis unfolding instance_of\<^sub>l\<^sub>s_def by auto
qed


subsection \<open>Merging substitutions\<close>

lemma project_sub:
  assumes inst_C:"C \<cdot>\<^sub>l\<^sub>s lmbd = C'" 
  assumes L'sub: "L' \<subseteq> C'"
  shows "\<exists>L \<subseteq> C. L \<cdot>\<^sub>l\<^sub>s lmbd = L' \<and> (C-L) \<cdot>\<^sub>l\<^sub>s lmbd = C' - L'"
proof -
  let ?L = "{l \<in> C. \<exists>l' \<in> L'. l \<cdot>\<^sub>l lmbd = l'}"
  have "?L \<subseteq> C" by auto
  moreover
  have "?L \<cdot>\<^sub>l\<^sub>s lmbd = L'"
    proof (rule Orderings.order_antisym; rule Set.subsetI)
      fix l'
      assume l'L: "l' \<in> L'"
      from inst_C have "{l \<cdot>\<^sub>l lmbd|l. l \<in> C} = C'" unfolding subls_def2 by -
      then have "\<exists>l. l' = l \<cdot>\<^sub>l lmbd \<and> l \<in> C \<and> l \<cdot>\<^sub>l lmbd \<in> L'" using L'sub l'L by auto
      then have " l' \<in> {l \<in> C. l \<cdot>\<^sub>l lmbd \<in> L'} \<cdot>\<^sub>l\<^sub>s lmbd" by auto
      then show " l' \<in> {l \<in> C. \<exists>l'\<in>L'. l \<cdot>\<^sub>l lmbd = l'} \<cdot>\<^sub>l\<^sub>s lmbd" by auto
    qed auto
  moreover
  have "(C-?L) \<cdot>\<^sub>l\<^sub>s lmbd = C' - L'" using inst_C by auto
  ultimately show ?thesis
    by blast    
qed

lemma relevant_vars_subt:
  assumes "\<forall>x \<in> vars\<^sub>t t. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  shows " t \<cdot>\<^sub>t \<sigma>\<^sub>1 = t \<cdot>\<^sub>t \<sigma>\<^sub>2"
using assms proof (induction t)
  case (Fun f ts)
  have f: "\<forall>t. t \<in> set ts \<longrightarrow> vars\<^sub>t t \<subseteq> vars\<^sub>t\<^sub>s ts" by (induction ts) auto
  have "\<forall>t\<in>set ts. t \<cdot>\<^sub>t \<sigma>\<^sub>1 = t \<cdot>\<^sub>t \<sigma>\<^sub>2" 
    proof
      fix t
      assume tints: "t \<in> set ts"
      then have "\<forall>x \<in> vars\<^sub>t t. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x" using f Fun(2) by auto
      then show "t \<cdot>\<^sub>t \<sigma>\<^sub>1 = t \<cdot>\<^sub>t \<sigma>\<^sub>2" using Fun tints by auto
    qed
  then have "ts \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>1 = ts \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>2" by auto
  then show ?case by auto
qed auto

lemma relevant_vars_subts: (* similar to above proof *)
  assumes asm: "\<forall>x \<in> vars\<^sub>t\<^sub>s ts. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  shows "ts \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>1 = ts \<cdot>\<^sub>t\<^sub>s \<sigma>\<^sub>2" 
proof -
   have f: "\<forall>t. t \<in> set ts \<longrightarrow> vars\<^sub>t t \<subseteq> vars\<^sub>t\<^sub>s ts" by (induction ts) auto
   have "\<forall>t\<in>set ts. t \<cdot>\<^sub>t \<sigma>\<^sub>1 = t \<cdot>\<^sub>t \<sigma>\<^sub>2" 
    proof
      fix t
      assume tints: "t \<in> set ts"
      then have "\<forall>x \<in> vars\<^sub>t t. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x" using f asm by auto
      then show "t \<cdot>\<^sub>t \<sigma>\<^sub>1 = t \<cdot>\<^sub>t \<sigma>\<^sub>2" using relevant_vars_subt tints by auto
    qed
  then show ?thesis by auto
qed

lemma relevant_vars_subl:
  assumes "\<forall>x \<in> vars\<^sub>l l. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x "
  shows "l \<cdot>\<^sub>l \<sigma>\<^sub>1 = l \<cdot>\<^sub>l \<sigma>\<^sub>2"
using assms proof (induction l)
  case (Pos p ts)
  then show ?case using relevant_vars_subts unfolding vars\<^sub>l_def by auto
next
  case (Neg p ts)
  then show ?case using relevant_vars_subts unfolding vars\<^sub>l_def by auto
qed

lemma relevant_vars_subls: (* in many ways a mirror of relevant_vars_subts  *)
  assumes asm: "\<forall>x \<in> vars\<^sub>l\<^sub>s L. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x"
  shows "L \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>1 = L \<cdot>\<^sub>l\<^sub>s \<sigma>\<^sub>2"
proof -
  have f: "\<forall>l. l \<in> L \<longrightarrow> vars\<^sub>l l \<subseteq> vars\<^sub>l\<^sub>s L" unfolding vars\<^sub>l\<^sub>s_def by auto
  have "\<forall>l \<in> L. l \<cdot>\<^sub>l \<sigma>\<^sub>1 = l \<cdot>\<^sub>l \<sigma>\<^sub>2"
    proof
      fix l
      assume linls: "l\<in>L"
      then have "\<forall>x\<in>vars\<^sub>l l. \<sigma>\<^sub>1 x = \<sigma>\<^sub>2 x" using f asm by auto
      then show "l \<cdot>\<^sub>l \<sigma>\<^sub>1 = l \<cdot>\<^sub>l \<sigma>\<^sub>2" using relevant_vars_subl linls by auto
    qed
  then show ?thesis by (meson image_cong) 
qed

lemma merge_sub:
  assumes dist: "vars\<^sub>l\<^sub>s C \<inter> vars\<^sub>l\<^sub>s D = {}"
  assumes CC': "C \<cdot>\<^sub>l\<^sub>s lmbd = C'"
  assumes DD': "D \<cdot>\<^sub>l\<^sub>s \<mu> = D'"
  shows "\<exists>\<eta>. C \<cdot>\<^sub>l\<^sub>s \<eta> = C' \<and> D \<cdot>\<^sub>l\<^sub>s \<eta> = D'"
proof -
  let ?\<eta> = "\<lambda>x. if x \<in> vars\<^sub>l\<^sub>s C then lmbd x else \<mu> x"
  have " \<forall>x\<in>vars\<^sub>l\<^sub>s C. ?\<eta> x = lmbd x" by auto
  then have "C \<cdot>\<^sub>l\<^sub>s ?\<eta> = C \<cdot>\<^sub>l\<^sub>s lmbd" using relevant_vars_subls[of C ?\<eta> lmbd] by auto
  then have "C \<cdot>\<^sub>l\<^sub>s ?\<eta> = C'" using CC' by auto
  moreover
  have " \<forall>x \<in> vars\<^sub>l\<^sub>s D. ?\<eta> x = \<mu> x" using dist by auto
  then have "D \<cdot>\<^sub>l\<^sub>s ?\<eta> = D \<cdot>\<^sub>l\<^sub>s \<mu>" using relevant_vars_subls[of D ?\<eta> \<mu>] by auto
  then have "D \<cdot>\<^sub>l\<^sub>s ?\<eta> = D'" using DD' by auto
  ultimately
  show ?thesis by auto
qed


subsection \<open>Standardizing apart\<close>

abbreviation std\<^sub>1 :: "fterm clause \<Rightarrow> fterm clause" where
  "std\<^sub>1 C \<equiv> C \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (''1'' @ x))"

abbreviation std\<^sub>2 :: "fterm clause \<Rightarrow> fterm clause" where
  "std\<^sub>2 C \<equiv> C \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (''2'' @ x))"

lemma std_apart_apart'': 
  assumes "x \<in> vars\<^sub>t  (t \<cdot>\<^sub>t (\<lambda>x::char list. Var (y @ x)))"
  shows "\<exists>x'. x = y@x'"
using assms by (induction t) auto

lemma std_apart_apart':
  assumes "x \<in> vars\<^sub>l (l \<cdot>\<^sub>l (\<lambda>x. Var  (y@x)))" 
  shows "\<exists>x'. x = y@x'"
using assms unfolding vars\<^sub>l_def using std_apart_apart'' by (cases l) auto

lemma std_apart_apart: "vars\<^sub>l\<^sub>s (std\<^sub>1 C\<^sub>1) \<inter> vars\<^sub>l\<^sub>s (std\<^sub>2 C\<^sub>2) = {}"
proof -
  {
    fix x
    assume xin: "x \<in> vars\<^sub>l\<^sub>s (std\<^sub>1 C\<^sub>1) \<inter> vars\<^sub>l\<^sub>s (std\<^sub>2 C\<^sub>2)"
    from xin have "x \<in> vars\<^sub>l\<^sub>s (std\<^sub>1 C\<^sub>1)" by auto
    then have "\<exists>x'. x=''1'' @ x'" 
      using std_apart_apart'[of x _ "''1''"] unfolding vars\<^sub>l\<^sub>s_def by auto
    moreover
    from xin have "x \<in> vars\<^sub>l\<^sub>s (std\<^sub>2 C\<^sub>2)" by auto
    then have "\<exists>x'. x= ''2'' @x' " 
      using std_apart_apart'[of x _ "''2''"] unfolding vars\<^sub>l\<^sub>s_def by auto
    ultimately have "False" by auto
    then have "x \<in> {}" by auto
  }
  then show ?thesis by auto 
qed

lemma std_apart_instance_of\<^sub>l\<^sub>s1: "instance_of\<^sub>l\<^sub>s C\<^sub>1 (std\<^sub>1 C\<^sub>1)"
proof -
  have empty: "(\<lambda>x. Var (''1''@x)) \<cdot> (\<lambda>x. Var (tl x)) = \<epsilon>" using composition_def by auto         

  have "C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<epsilon> = C\<^sub>1" using empty_subls by auto
  then have "C\<^sub>1 \<cdot>\<^sub>l\<^sub>s ((\<lambda>x. Var (''1''@x)) \<cdot> (\<lambda>x. Var (tl x))) = C\<^sub>1" using empty by auto
  then have "(C\<^sub>1 \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (''1''@x))) \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (tl x)) = C\<^sub>1" using composition_conseq2ls by auto
  then have "C\<^sub>1 = (std\<^sub>1 C\<^sub>1) \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (tl x))" by auto
  then show "instance_of\<^sub>l\<^sub>s C\<^sub>1 (std\<^sub>1 C\<^sub>1)" unfolding instance_of\<^sub>l\<^sub>s_def by auto
qed

lemma std_apart_instance_of\<^sub>l\<^sub>s2: "instance_of\<^sub>l\<^sub>s C2 (std\<^sub>2 C2)"  
proof -
  have empty: "(\<lambda>x. Var (''2''@x)) \<cdot> (\<lambda>x. Var (tl x)) = \<epsilon>" using composition_def by auto

  have "C2 \<cdot>\<^sub>l\<^sub>s \<epsilon> = C2" using empty_subls by auto
  then have "C2 \<cdot>\<^sub>l\<^sub>s ((\<lambda>x. Var (''2''@x)) \<cdot> (\<lambda>x. Var (tl x))) = C2" using empty by auto
  then have "(C2 \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (''2''@x))) \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (tl x)) = C2" using composition_conseq2ls by auto
  then have "C2 = (std\<^sub>2 C2) \<cdot>\<^sub>l\<^sub>s (\<lambda>x. Var (tl x))" by auto
  then show "instance_of\<^sub>l\<^sub>s C2 (std\<^sub>2 C2)" unfolding instance_of\<^sub>l\<^sub>s_def by auto
qed


section \<open>Unifiers\<close>

definition unifier\<^sub>t\<^sub>s :: "substitution \<Rightarrow> fterm set \<Rightarrow> bool" where
  "unifier\<^sub>t\<^sub>s \<sigma> ts \<longleftrightarrow> (\<exists>t'. \<forall>t \<in> ts. t \<cdot>\<^sub>t \<sigma> = t')"

definition unifier\<^sub>l\<^sub>s :: "substitution \<Rightarrow> fterm literal set \<Rightarrow> bool" where
  "unifier\<^sub>l\<^sub>s \<sigma> L \<longleftrightarrow> (\<exists>l'. \<forall>l \<in> L. l \<cdot>\<^sub>l \<sigma> = l')"

lemma unif_sub:
  assumes unif: "unifier\<^sub>l\<^sub>s \<sigma> L"
  assumes nonempty: "L \<noteq> {}"
  shows "\<exists>l. subls L \<sigma> = {subl l \<sigma>}"
proof -
  from nonempty obtain l where "l \<in> L" by auto
  from unif this have "L \<cdot>\<^sub>l\<^sub>s \<sigma> = {l \<cdot>\<^sub>l \<sigma>}" unfolding unifier\<^sub>l\<^sub>s_def by auto
  then show ?thesis by auto
qed

lemma unifiert_def2: (*  (\<lambda>t. sub t \<sigma>) ` ts could have some nice notation maybe *)
  assumes L_elem: "ts \<noteq> {}"
  shows "unifier\<^sub>t\<^sub>s \<sigma> ts \<longleftrightarrow> (\<exists>l. (\<lambda>t. sub t \<sigma>) ` ts ={l})"
proof
  assume unif: "unifier\<^sub>t\<^sub>s \<sigma> ts"
  from L_elem obtain t where "t \<in> ts" by auto
  then have "(\<lambda>t. sub t \<sigma>) ` ts = {t \<cdot>\<^sub>t \<sigma>}" using unif unfolding unifier\<^sub>t\<^sub>s_def by auto
  then show "\<exists>l. (\<lambda>t. sub t \<sigma>) ` ts = {l}" by auto
next
  assume "\<exists>l. (\<lambda>t. sub t \<sigma>) ` ts ={l}"
  then obtain l where "(\<lambda>t. sub t \<sigma>) ` ts = {l}" by auto
  then have "\<forall>l' \<in> ts. l' \<cdot>\<^sub>t \<sigma> = l" by auto
  then show "unifier\<^sub>t\<^sub>s \<sigma> ts" unfolding unifier\<^sub>t\<^sub>s_def by auto
qed

lemma unifier\<^sub>l\<^sub>s_def2: 
  assumes L_elem: "L \<noteq> {}"
  shows "unifier\<^sub>l\<^sub>s \<sigma> L \<longleftrightarrow> (\<exists>l. L \<cdot>\<^sub>l\<^sub>s \<sigma> = {l})"
proof
  assume unif: "unifier\<^sub>l\<^sub>s \<sigma> L"
  from L_elem obtain l where "l \<in> L" by auto
  then have "L \<cdot>\<^sub>l\<^sub>s \<sigma> = {l \<cdot>\<^sub>l \<sigma>}" using unif unfolding unifier\<^sub>l\<^sub>s_def by auto
  then show "\<exists>l. L \<cdot>\<^sub>l\<^sub>s \<sigma> = {l}" by auto
next
  assume "\<exists>l. L \<cdot>\<^sub>l\<^sub>s \<sigma> ={l}"
  then obtain l where "L \<cdot>\<^sub>l\<^sub>s \<sigma> = {l}" by auto
  then have "\<forall>l' \<in> L. l' \<cdot>\<^sub>l \<sigma> = l" by auto
  then show "unifier\<^sub>l\<^sub>s \<sigma> L" unfolding unifier\<^sub>l\<^sub>s_def by auto
qed

lemma ground\<^sub>l\<^sub>s_unif_singleton:
  assumes ground\<^sub>l\<^sub>s: "ground\<^sub>l\<^sub>s L" 
  assumes unif: "unifier\<^sub>l\<^sub>s \<sigma>' L"
  assumes empt: "L \<noteq> {}"
  shows "\<exists>l. L = {l}"
proof -
  from unif empt have "\<exists>l. L \<cdot>\<^sub>l\<^sub>s \<sigma>' = {l}" using unif_sub by auto
  then show ?thesis using ground\<^sub>l\<^sub>s_subls ground\<^sub>l\<^sub>s by auto
qed

definition unifiablets :: "fterm set \<Rightarrow> bool" where
  "unifiablets fs \<longleftrightarrow> (\<exists>\<sigma>. unifier\<^sub>t\<^sub>s \<sigma> fs)"

definition unifiablels :: "fterm literal set \<Rightarrow> bool" where
  "unifiablels L \<longleftrightarrow> (\<exists>\<sigma>. unifier\<^sub>l\<^sub>s \<sigma> L)"

lemma unifier_comp[simp]: "unifier\<^sub>l\<^sub>s \<sigma> (L\<^sup>C) \<longleftrightarrow> unifier\<^sub>l\<^sub>s \<sigma> L"
proof
  assume "unifier\<^sub>l\<^sub>s \<sigma> (L\<^sup>C)" 
  then obtain l'' where l''_p: "\<forall>l \<in> L\<^sup>C. l \<cdot>\<^sub>l \<sigma> = l''" 
    unfolding unifier\<^sub>l\<^sub>s_def by auto
  obtain l' where "(l')\<^sup>c = l''" using comp_exi2[of l''] by auto
  from this l''_p have l'_p:"\<forall>l \<in> L\<^sup>C. l \<cdot>\<^sub>l \<sigma> = (l')\<^sup>c" by auto
  have "\<forall>l \<in> L. l \<cdot>\<^sub>l \<sigma> = l'"
    proof
      fix l
      assume "l\<in>L"
      then have "l\<^sup>c \<in> L\<^sup>C" by auto
      then have "(l\<^sup>c) \<cdot>\<^sub>l \<sigma> = (l')\<^sup>c" using l'_p by auto
      then have "(l \<cdot>\<^sub>l \<sigma>)\<^sup>c = (l')\<^sup>c" by (cases l) auto
      then show "l \<cdot>\<^sub>l \<sigma> = l'" using cancel_comp2 by blast
    qed
  then show "unifier\<^sub>l\<^sub>s \<sigma> L" unfolding unifier\<^sub>l\<^sub>s_def by auto
next
  assume "unifier\<^sub>l\<^sub>s \<sigma> L"
  then obtain l' where l'_p: "\<forall>l \<in> L. l \<cdot>\<^sub>l \<sigma> = l'" unfolding unifier\<^sub>l\<^sub>s_def by auto
  have "\<forall>l \<in> L\<^sup>C. l \<cdot>\<^sub>l \<sigma> = (l')\<^sup>c"
    proof
      fix l
      assume "l \<in> L\<^sup>C"
      then have "l\<^sup>c \<in> L" using cancel_comp1 by (metis image_iff)
      then show "l \<cdot>\<^sub>l \<sigma> = (l')\<^sup>c" using l'_p comp_sub cancel_comp1 by metis
    qed
  then show "unifier\<^sub>l\<^sub>s \<sigma> (L\<^sup>C)" unfolding unifier\<^sub>l\<^sub>s_def by auto
qed

lemma unifier_sub1: 
  assumes "unifier\<^sub>l\<^sub>s \<sigma> L"
  assumes "L' \<subseteq> L"
  shows "unifier\<^sub>l\<^sub>s \<sigma> L' " 
  using assms unfolding unifier\<^sub>l\<^sub>s_def by auto

lemma unifier_sub2: 
  assumes asm: "unifier\<^sub>l\<^sub>s \<sigma> (L\<^sub>1 \<union> L\<^sub>2)"
  shows "unifier\<^sub>l\<^sub>s \<sigma> L\<^sub>1 \<and> unifier\<^sub>l\<^sub>s \<sigma> L\<^sub>2 "
proof -
  have "L\<^sub>1 \<subseteq> (L\<^sub>1 \<union> L\<^sub>2) \<and> L\<^sub>2 \<subseteq> (L\<^sub>1 \<union> L\<^sub>2)" by simp
  from this asm show ?thesis using unifier_sub1 by auto
qed


subsection \<open>Most General Unifiers\<close>

definition mgu\<^sub>t\<^sub>s :: "substitution \<Rightarrow> fterm set \<Rightarrow> bool" where
  "mgu\<^sub>t\<^sub>s \<sigma> ts \<longleftrightarrow> unifier\<^sub>t\<^sub>s \<sigma> ts \<and> (\<forall>u. unifier\<^sub>t\<^sub>s u ts \<longrightarrow> (\<exists>i. u = \<sigma> \<cdot> i))"

definition mgu\<^sub>l\<^sub>s :: "substitution \<Rightarrow> fterm literal set \<Rightarrow> bool" where
  "mgu\<^sub>l\<^sub>s \<sigma> L \<longleftrightarrow> unifier\<^sub>l\<^sub>s \<sigma> L \<and> (\<forall>u. unifier\<^sub>l\<^sub>s u L \<longrightarrow> (\<exists>i. u = \<sigma> \<cdot> i))"


section \<open>Resolution\<close>

definition applicable :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> bool" where
  "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<longleftrightarrow> 
       C\<^sub>1 \<noteq> {} \<and> C\<^sub>2 \<noteq> {} \<and> L\<^sub>1 \<noteq> {} \<and> L\<^sub>2 \<noteq> {}
     \<and> vars\<^sub>l\<^sub>s C\<^sub>1 \<inter> vars\<^sub>l\<^sub>s C\<^sub>2 = {} 
     \<and> L\<^sub>1 \<subseteq> C\<^sub>1 \<and> L\<^sub>2 \<subseteq> C\<^sub>2 
     \<and> mgu\<^sub>l\<^sub>s \<sigma> (L\<^sub>1 \<union> L\<^sub>2\<^sup>C)"

definition mresolution :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> fterm clause" where
  "mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = ((C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>)- (L\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>)) \<union> ((C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>) - (L\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>))"

definition resolution :: "   fterm clause \<Rightarrow> fterm clause 
                          \<Rightarrow> fterm literal set \<Rightarrow> fterm literal set 
                          \<Rightarrow> substitution \<Rightarrow> fterm clause" where
  "resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> = ((C\<^sub>1 - L\<^sub>1) \<union> (C\<^sub>2 - L\<^sub>2)) \<cdot>\<^sub>l\<^sub>s \<sigma>"

inductive mresolution_step :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  mresolution_rule:
    "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<Longrightarrow> 
       mresolution_step Cs (Cs \<union> {mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>})"
| standardize_apart:
    "C \<in> Cs \<Longrightarrow> var_renaming_of C C' \<Longrightarrow> mresolution_step Cs (Cs \<union> {C'})"

inductive resolution_step :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  resolution_rule: 
    "C\<^sub>1 \<in> Cs \<Longrightarrow> C\<^sub>2 \<in> Cs \<Longrightarrow> applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<Longrightarrow> 
       resolution_step Cs (Cs \<union> {resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>})"
| standardize_apart: (* renaming *)
    "C \<in> Cs \<Longrightarrow> var_renaming_of C C' \<Longrightarrow> resolution_step Cs (Cs \<union> {C'})"

definition mresolution_deriv :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "mresolution_deriv = rtranclp mresolution_step"

definition resolution_deriv :: "fterm clause set \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "resolution_deriv = rtranclp resolution_step"


section \<open>Soundness\<close>

definition evalsub :: "'u var_denot \<Rightarrow> 'u fun_denot \<Rightarrow> substitution \<Rightarrow> 'u var_denot" where
  "evalsub E F \<sigma> = eval\<^sub>t E F \<circ> \<sigma>"

lemma substitutiont: "eval\<^sub>t E F (t \<cdot>\<^sub>t \<sigma>) = eval\<^sub>t (evalsub E F \<sigma>) F t"
apply (induction t)
 unfolding evalsub_def apply auto
apply (metis (mono_tags, lifting) comp_apply map_cong)
done

lemma substitutionts: "eval\<^sub>t\<^sub>s E F (ts \<cdot>\<^sub>t\<^sub>s \<sigma>) = eval\<^sub>t\<^sub>s (evalsub E F \<sigma>) F ts"
using substitutiont by auto

lemma substitution: "eval\<^sub>l E F G (l \<cdot>\<^sub>l \<sigma>) \<longleftrightarrow> eval\<^sub>l (evalsub E F \<sigma>) F G l"
apply (induction l) 
 using substitutionts apply (metis eval\<^sub>l.simps(1) subl.simps(1)) 
using substitutionts apply (metis eval\<^sub>l.simps(2) subl.simps(2))
done

lemma subst_sound:
 assumes asm: "eval\<^sub>c F G C"
 shows "eval\<^sub>c F G (C \<cdot>\<^sub>l\<^sub>s \<sigma>)"
unfolding eval\<^sub>c_def proof
  fix E
  from asm have "\<forall>E'. \<exists>l \<in> C. eval\<^sub>l E' F G l" using eval\<^sub>c_def by blast
  then have "\<exists>l \<in> C. eval\<^sub>l (evalsub E F \<sigma>) F G l" by auto
  then show "\<exists>l \<in> C \<cdot>\<^sub>l\<^sub>s \<sigma>. eval\<^sub>l E F G l" using substitution by blast
qed

lemma simple_resolution_sound:
  assumes C\<^sub>1sat:  "eval\<^sub>c F G C\<^sub>1"
  assumes C\<^sub>2sat:  "eval\<^sub>c F G C\<^sub>2"
  assumes l\<^sub>1inc\<^sub>1: "l\<^sub>1 \<in> C\<^sub>1"
  assumes l\<^sub>2inc\<^sub>2: "l\<^sub>2 \<in> C\<^sub>2"
  assumes comp: "l\<^sub>1\<^sup>c = l\<^sub>2"
  shows "eval\<^sub>c F G ((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))"
proof -
  have "\<forall>E. \<exists>l \<in> (((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))). eval\<^sub>l E F G l"
    proof
      fix E
      have "eval\<^sub>l E F G l\<^sub>1 \<or> eval\<^sub>l E F G l\<^sub>2" using comp by (cases l\<^sub>1) auto
      then show "\<exists>l \<in> (((C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}))). eval\<^sub>l E F G l"
        proof
          assume "eval\<^sub>l E F G l\<^sub>1"
          then have "\<not>eval\<^sub>l E F G l\<^sub>2" using comp by (cases l\<^sub>1) auto
          then have "\<exists>l\<^sub>2'\<in> C\<^sub>2. l\<^sub>2' \<noteq> l\<^sub>2 \<and> eval\<^sub>l E F G l\<^sub>2'" using l\<^sub>2inc\<^sub>2 C\<^sub>2sat unfolding eval\<^sub>c_def by auto
          then show "\<exists>l\<in>(C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}). eval\<^sub>l E F G l" by auto
        next
          assume "eval\<^sub>l E F G l\<^sub>2" (* Symmetric *)
          then have "\<not>eval\<^sub>l E F G l\<^sub>1" using comp by (cases l\<^sub>1) auto
          then have "\<exists>l\<^sub>1'\<in> C\<^sub>1. l\<^sub>1' \<noteq> l\<^sub>1 \<and> eval\<^sub>l E F G l\<^sub>1'" using l\<^sub>1inc\<^sub>1 C\<^sub>1sat unfolding eval\<^sub>c_def by auto
          then show "\<exists>l\<in>(C\<^sub>1 - {l\<^sub>1}) \<union> (C\<^sub>2 - {l\<^sub>2}). eval\<^sub>l E F G l" by auto
        qed
    qed
  then show ?thesis unfolding eval\<^sub>c_def by simp
qed

lemma mresolution_sound:
  assumes sat\<^sub>1: "eval\<^sub>c F G C\<^sub>1"
  assumes sat\<^sub>2: "eval\<^sub>c F G C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "eval\<^sub>c F G (mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from sat\<^sub>1 have sat\<^sub>1\<sigma>: "eval\<^sub>c F G (C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>)" using subst_sound by blast
  from sat\<^sub>2 have sat\<^sub>2\<sigma>: "eval\<^sub>c F G (C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>)" using subst_sound by blast

  from appl obtain l\<^sub>1 where l\<^sub>1_p: "l\<^sub>1 \<in> L\<^sub>1" unfolding applicable_def by auto

  from l\<^sub>1_p appl have "l\<^sub>1 \<in> C\<^sub>1" unfolding applicable_def by auto
  then have inc\<^sub>1\<sigma>: "l\<^sub>1 \<cdot>\<^sub>l \<sigma> \<in> C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>" by auto
  
  from l\<^sub>1_p have unified\<^sub>1: "l\<^sub>1 \<in> (L\<^sub>1 \<union> (L\<^sub>2\<^sup>C))" by auto

  from l\<^sub>1_p appl have l\<^sub>1\<sigma>isl\<^sub>1\<sigma>: "{l\<^sub>1 \<cdot>\<^sub>l \<sigma>} = L\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>"  
    unfolding mgu\<^sub>l\<^sub>s_def unifier\<^sub>l\<^sub>s_def applicable_def by auto

  from appl obtain l\<^sub>2 where l\<^sub>2_p: "l\<^sub>2 \<in> L\<^sub>2" unfolding applicable_def by auto
  
  from l\<^sub>2_p appl have "l\<^sub>2 \<in> C\<^sub>2" unfolding applicable_def by auto
  then have inc\<^sub>2\<sigma>: "l\<^sub>2 \<cdot>\<^sub>l \<sigma> \<in> C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>" by auto

  from l\<^sub>2_p have unified\<^sub>2: "l\<^sub>2\<^sup>c \<in> (L\<^sub>1 \<union> (L\<^sub>2\<^sup>C))" by auto

  from unified\<^sub>1 unified\<^sub>2 appl have "l\<^sub>1 \<cdot>\<^sub>l \<sigma> = (l\<^sub>2\<^sup>c) \<cdot>\<^sub>l \<sigma>" 
    unfolding mgu\<^sub>l\<^sub>s_def unifier\<^sub>l\<^sub>s_def applicable_def by auto
  then have comp: "(l\<^sub>1 \<cdot>\<^sub>l \<sigma>)\<^sup>c = l\<^sub>2 \<cdot>\<^sub>l \<sigma>" using comp_sub comp_swap by auto 

  from appl have "unifier\<^sub>l\<^sub>s \<sigma> (L\<^sub>2\<^sup>C)" 
    using unifier_sub2 unfolding mgu\<^sub>l\<^sub>s_def applicable_def by blast
  then have "unifier\<^sub>l\<^sub>s \<sigma> L\<^sub>2" by auto
  from this l\<^sub>2_p have l\<^sub>2\<sigma>isl\<^sub>2\<sigma>: "{l\<^sub>2 \<cdot>\<^sub>l \<sigma>} = L\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>" unfolding unifier\<^sub>l\<^sub>s_def by auto

  from sat\<^sub>1\<sigma> sat\<^sub>2\<sigma> inc\<^sub>1\<sigma> inc\<^sub>2\<sigma> comp have "eval\<^sub>c F G ((C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>) - {l\<^sub>1 \<cdot>\<^sub>l \<sigma>} \<union> ((C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>) - {l\<^sub>2 \<cdot>\<^sub>l \<sigma>}))" using simple_resolution_sound[of F G "C\<^sub>1 \<cdot>\<^sub>l\<^sub>s \<sigma>" "C\<^sub>2 \<cdot>\<^sub>l\<^sub>s \<sigma>" "l\<^sub>1 \<cdot>\<^sub>l \<sigma>" " l\<^sub>2 \<cdot>\<^sub>l \<sigma>"]
    by auto
  from this l\<^sub>1\<sigma>isl\<^sub>1\<sigma> l\<^sub>2\<sigma>isl\<^sub>2\<sigma> show ?thesis unfolding mresolution_def by auto
qed

lemma resolution_superset: "mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma> \<subseteq> resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
 unfolding mresolution_def resolution_def by auto

lemma superset_sound:
  assumes sup: "C \<subseteq> C'"
  assumes sat: "eval\<^sub>c F G C"
  shows "eval\<^sub>c F G C'"
proof -
  have "\<forall>E. \<exists>l \<in> C'. eval\<^sub>l E F G l"
    proof
      fix E
      from sat have "\<forall>E. \<exists>l \<in> C. eval\<^sub>l E F G l" unfolding eval\<^sub>c_def by -
      then have "\<exists>l \<in> C . eval\<^sub>l E F G l" by auto
      then show "\<exists>l \<in> C'. eval\<^sub>l E F G l" using sup by auto
    qed
  then show "eval\<^sub>c F G C'" unfolding eval\<^sub>c_def by auto
qed
 
theorem resolution_sound:
  assumes sat\<^sub>1: "eval\<^sub>c F G C\<^sub>1"
  assumes sat\<^sub>2: "eval\<^sub>c F G C\<^sub>2"
  assumes appl: "applicable C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>"
  shows "eval\<^sub>c F G (resolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)"
proof -
  from sat\<^sub>1 sat\<^sub>2 appl have "eval\<^sub>c F G (mresolution C\<^sub>1 C\<^sub>2 L\<^sub>1 L\<^sub>2 \<sigma>)" using mresolution_sound by blast
  then show ?thesis using superset_sound resolution_superset by metis
qed

lemma mstep_sound: 
  assumes "mresolution_step Cs Cs'"
  assumes "eval\<^sub>c\<^sub>s F G Cs"
  shows "eval\<^sub>c\<^sub>s F G Cs'"
using assms proof (induction rule: mresolution_step.induct)
  case (mresolution_rule C\<^sub>1 Cs C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)
  then have "eval\<^sub>c F G C\<^sub>1 \<and> eval\<^sub>c F G C\<^sub>2" unfolding eval\<^sub>c\<^sub>s_def by auto
  then have "eval\<^sub>c F G (mresolution C\<^sub>1 C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)" 
    using mresolution_sound mresolution_rule by auto
  then show ?case using mresolution_rule unfolding eval\<^sub>c\<^sub>s_def by auto
next
  case (standardize_apart C Cs C')
  then have "eval\<^sub>c F G C" unfolding eval\<^sub>c\<^sub>s_def by auto
  then have "eval\<^sub>c F G C'" using subst_sound standardize_apart unfolding var_renaming_of_def instance_of\<^sub>l\<^sub>s_def by metis
  then show ?case using standardize_apart unfolding eval\<^sub>c\<^sub>s_def by auto
qed

theorem step_sound: 
  assumes "resolution_step Cs Cs'"
  assumes "eval\<^sub>c\<^sub>s F G Cs"
  shows "eval\<^sub>c\<^sub>s F G Cs'"
using assms proof (induction rule: resolution_step.induct)
  case (resolution_rule C\<^sub>1 Cs C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)
  then have "eval\<^sub>c F G C\<^sub>1 \<and> eval\<^sub>c F G C\<^sub>2" unfolding eval\<^sub>c\<^sub>s_def by auto
  then have "eval\<^sub>c F G (resolution C\<^sub>1 C\<^sub>2 l\<^sub>1 l\<^sub>2 \<sigma>)" 
    using resolution_sound resolution_rule by auto
  then show ?case using resolution_rule unfolding eval\<^sub>c\<^sub>s_def by auto
next
  case (standardize_apart C Cs C')
  then have "eval\<^sub>c F G C" unfolding eval\<^sub>c\<^sub>s_def by auto
  then have "eval\<^sub>c F G C'" using subst_sound standardize_apart unfolding var_renaming_of_def instance_of\<^sub>l\<^sub>s_def by metis
  then show ?case using standardize_apart unfolding eval\<^sub>c\<^sub>s_def by auto
qed

lemma mderivation_sound: 
  assumes "mresolution_deriv Cs Cs'"
  assumes "eval\<^sub>c\<^sub>s F G Cs"
  shows "eval\<^sub>c\<^sub>s F G Cs'" 
using assms unfolding mresolution_deriv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl then show ?case by auto
next
  case (rtrancl_into_rtrancl Cs\<^sub>1 Cs\<^sub>2 Cs\<^sub>3) then show ?case using mstep_sound by auto
qed

theorem derivation_sound: 
  assumes "resolution_deriv Cs Cs'"
  assumes "eval\<^sub>c\<^sub>s F G Cs"
  shows"eval\<^sub>c\<^sub>s F G Cs'" 
using assms unfolding resolution_deriv_def
proof (induction rule: rtranclp.induct)
  case rtrancl_refl then show ?case by auto
next
  case (rtrancl_into_rtrancl Cs\<^sub>1 Cs\<^sub>2 Cs\<^sub>3) then show ?case using step_sound by auto
qed
  
theorem derivation_sound_refute: 
  assumes deriv: "resolution_deriv Cs Cs' \<and> {} \<in> Cs'"
  shows "\<not>eval\<^sub>c\<^sub>s F G Cs"
proof -
  from deriv have "eval\<^sub>c\<^sub>s F G Cs \<longrightarrow> eval\<^sub>c\<^sub>s F G Cs'" using derivation_sound by auto
  moreover
  from deriv have "eval\<^sub>c\<^sub>s F G Cs' \<longrightarrow> eval\<^sub>c F G {}" unfolding eval\<^sub>c\<^sub>s_def by auto
  moreover
  then have "eval\<^sub>c F G {} \<longrightarrow> False" unfolding eval\<^sub>c_def by auto
  ultimately show ?thesis by auto
qed


section \<open>Herbrand Interpretations\<close>

text \<open>@{const HFun} is the Herbrand function denotation in which terms are mapped to themselves.\<close>
term HFun

lemma eval_ground\<^sub>t: 
  assumes "ground\<^sub>t t"
  shows "(eval\<^sub>t E HFun t) = hterm_of_fterm t"
  using assms by (induction t) auto


lemma eval_ground\<^sub>t\<^sub>s: 
  assumes "ground\<^sub>t\<^sub>s ts"
  shows "(eval\<^sub>t\<^sub>s E HFun ts) = hterms_of_fterms ts" 
  unfolding hterms_of_fterms_def using assms eval_ground\<^sub>t by (induction ts) auto

lemma eval\<^sub>l_ground\<^sub>t\<^sub>s:
  assumes asm: "ground\<^sub>t\<^sub>s ts"
  shows "eval\<^sub>l E HFun G (Pos P ts) \<longleftrightarrow> G P (hterms_of_fterms ts)"
proof -
  have "eval\<^sub>l E HFun G (Pos P ts) = G P (eval\<^sub>t\<^sub>s E HFun ts)" by auto
  also have "... = G P (hterms_of_fterms ts)" using asm eval_ground\<^sub>t\<^sub>s by simp 
  finally show ?thesis by auto
qed


section \<open>Partial Interpretations\<close>

type_synonym partial_pred_denot = "bool list"

definition falsifies\<^sub>l :: "partial_pred_denot \<Rightarrow> fterm literal \<Rightarrow> bool" where
  "falsifies\<^sub>l G l \<longleftrightarrow>
        ground\<^sub>l l
     \<and> (let i = nat_of_fatom (get_atom l) in
          i < length G \<and> G ! i = (\<not>sign l)
        )"

text \<open>A ground clause is falsified if it is actually ground and all its literals are falsified.\<close>
abbreviation falsifies\<^sub>g :: "partial_pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "falsifies\<^sub>g G C \<equiv> ground\<^sub>l\<^sub>s C \<and> (\<forall>l \<in> C. falsifies\<^sub>l G l)"

abbreviation falsifies\<^sub>c :: "partial_pred_denot \<Rightarrow> fterm clause \<Rightarrow> bool" where
  "falsifies\<^sub>c G C \<equiv> (\<exists>C'. instance_of\<^sub>l\<^sub>s C' C \<and> falsifies\<^sub>g G C')"

abbreviation falsifies\<^sub>c\<^sub>s :: "partial_pred_denot \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "falsifies\<^sub>c\<^sub>s G Cs \<equiv> (\<exists>C \<in> Cs. falsifies\<^sub>c G C)"  

abbreviation extend :: "(nat \<Rightarrow> partial_pred_denot) \<Rightarrow> hterm pred_denot" where
  "extend f P ts \<equiv> (
     let n = nat_of_hatom (P, ts) in
       f (Suc n) ! n
     )"

fun sub_of_denot :: "hterm var_denot \<Rightarrow> substitution" where
  "sub_of_denot E = fterm_of_hterm \<circ> E"

lemma ground_sub_of_denott: "ground\<^sub>t (t \<cdot>\<^sub>t (sub_of_denot E))" 
  by (induction t) (auto simp add: ground_fterm_of_hterm)


lemma ground_sub_of_denotts: "ground\<^sub>t\<^sub>s (ts \<cdot>\<^sub>t\<^sub>s sub_of_denot E)"
using ground_sub_of_denott by simp 


lemma ground_sub_of_denotl: "ground\<^sub>l (l \<cdot>\<^sub>l sub_of_denot E)"
proof -
  have "ground\<^sub>t\<^sub>s (subs (get_terms l) (sub_of_denot E))" 
    using ground_sub_of_denotts by auto
  then show ?thesis by (cases l)  auto
qed

lemma sub_of_denot_equivx: "eval\<^sub>t E HFun (sub_of_denot E x) = E x"
proof -
  have "ground\<^sub>t (sub_of_denot E x)" using ground_fterm_of_hterm by simp
  then
  have "eval\<^sub>t E HFun (sub_of_denot E x) = hterm_of_fterm (sub_of_denot E x)"
    using eval_ground\<^sub>t(1) by auto
  also have "... = hterm_of_fterm (fterm_of_hterm (E x))" by auto
  also have "... = E x" by auto
  finally show ?thesis by auto
qed

lemma sub_of_denot_equivt:
    "eval\<^sub>t E HFun (t \<cdot>\<^sub>t (sub_of_denot E)) = eval\<^sub>t E HFun t"
using sub_of_denot_equivx  by (induction t) auto

lemma sub_of_denot_equivts: "eval\<^sub>t\<^sub>s E HFun (ts \<cdot>\<^sub>t\<^sub>s (sub_of_denot E)) = eval\<^sub>t\<^sub>s E HFun ts"
using sub_of_denot_equivt by simp

lemma sub_of_denot_equivl: "eval\<^sub>l E HFun G (l \<cdot>\<^sub>l sub_of_denot E) \<longleftrightarrow> eval\<^sub>l E HFun G l"
proof (induction l)
  case (Pos p ts)
  have "eval\<^sub>l E HFun G ((Pos p ts) \<cdot>\<^sub>l sub_of_denot E) \<longleftrightarrow> G p (eval\<^sub>t\<^sub>s E HFun (ts \<cdot>\<^sub>t\<^sub>s (sub_of_denot E)))" by auto
  also have " ... \<longleftrightarrow> G p (eval\<^sub>t\<^sub>s E HFun ts)" using sub_of_denot_equivts[of E ts] by metis
  also have " ... \<longleftrightarrow> eval\<^sub>l E HFun G (Pos p ts)" by simp
  finally
  show ?case by blast
next
 case (Neg p ts)
  have "eval\<^sub>l E HFun G ((Neg p ts) \<cdot>\<^sub>l sub_of_denot E) \<longleftrightarrow> \<not>G p (eval\<^sub>t\<^sub>s E HFun (ts \<cdot>\<^sub>t\<^sub>s (sub_of_denot E)))" by auto
  also have " ... \<longleftrightarrow> \<not>G p (eval\<^sub>t\<^sub>s E HFun ts)" using sub_of_denot_equivts[of E ts] by metis
  also have " ... = eval\<^sub>l E HFun G (Neg p ts)" by simp
  finally
  show ?case by blast
qed

text \<open>Under an Herbrand interpretation, an environment is equivalent to a substitution.\<close>
lemma sub_of_denot_equiv_ground': 
  "eval\<^sub>l E HFun G l = eval\<^sub>l E HFun G (l \<cdot>\<^sub>l sub_of_denot E) \<and> ground\<^sub>l (l \<cdot>\<^sub>l sub_of_denot E)"
    using sub_of_denot_equivl ground_sub_of_denotl by auto

text \<open>Under an Herbrand interpretation, an environment is similar to a substitution - also for partial interpretations.\<close>
lemma partial_equiv_subst:
  assumes "falsifies\<^sub>c G (C \<cdot>\<^sub>l\<^sub>s \<tau>)"
  shows "falsifies\<^sub>c G C"
proof -
  from assms obtain C' where C'_p: "instance_of\<^sub>l\<^sub>s C' (C \<cdot>\<^sub>l\<^sub>s \<tau>) \<and> falsifies\<^sub>g G C'" by auto
  then have "instance_of\<^sub>l\<^sub>s (C \<cdot>\<^sub>l\<^sub>s \<tau>) C" unfolding instance_of\<^sub>l\<^sub>s_def by auto
  then have "instance_of\<^sub>l\<^sub>s C' C" using C'_p instance_of\<^sub>l\<^sub>s_trans by auto
  then show ?thesis using C'_p by auto
qed

text \<open>Under an Herbrand interpretation, an environment is equivalent to a substitution.\<close>
lemma sub_of_denot_equiv_ground:
  "((\<exists>l \<in> C. eval\<^sub>l E HFun G l) \<longleftrightarrow> (\<exists>l \<in> C \<cdot>\<^sub>l\<^sub>s sub_of_denot E. eval\<^sub>l E HFun G l))
           \<and> ground\<^sub>l\<^sub>s (C \<cdot>\<^sub>l\<^sub>s sub_of_denot E)"
  using sub_of_denot_equiv_ground' by auto

lemma std\<^sub>1_falsifies: "falsifies\<^sub>c G C\<^sub>1 \<longleftrightarrow> falsifies\<^sub>c G (std\<^sub>1 C\<^sub>1)"
proof 
  assume asm: "falsifies\<^sub>c G C\<^sub>1"
  then obtain Cg where "instance_of\<^sub>l\<^sub>s Cg C\<^sub>1  \<and> falsifies\<^sub>g G Cg" by auto
  moreover
  then have "instance_of\<^sub>l\<^sub>s Cg (std\<^sub>1 C\<^sub>1)" using std_apart_instance_of\<^sub>l\<^sub>s1 instance_of\<^sub>l\<^sub>s_trans by blast
  ultimately
  show "falsifies\<^sub>c G (std\<^sub>1 C\<^sub>1)" by auto
next
  assume asm: "falsifies\<^sub>c G (std\<^sub>1 C\<^sub>1)"
  then have inst: "instance_of\<^sub>l\<^sub>s (std\<^sub>1 C\<^sub>1) C\<^sub>1" unfolding instance_of\<^sub>l\<^sub>s_def by auto

  from asm obtain Cg where "instance_of\<^sub>l\<^sub>s Cg (std\<^sub>1 C\<^sub>1)  \<and> falsifies\<^sub>g G Cg" by auto
  moreover
  then have "instance_of\<^sub>l\<^sub>s Cg C\<^sub>1" using inst instance_of\<^sub>l\<^sub>s_trans by blast
  ultimately
  show "falsifies\<^sub>c G C\<^sub>1" by auto
qed

lemma std\<^sub>2_falsifies: "falsifies\<^sub>c G C\<^sub>2 \<longleftrightarrow> falsifies\<^sub>c G (std\<^sub>2 C\<^sub>2)"
proof 
  assume asm: "falsifies\<^sub>c G C\<^sub>2"
  then obtain Cg where "instance_of\<^sub>l\<^sub>s Cg C\<^sub>2  \<and> falsifies\<^sub>g G Cg" by auto
  moreover
  then have "instance_of\<^sub>l\<^sub>s Cg (std\<^sub>2 C\<^sub>2)" using std_apart_instance_of\<^sub>l\<^sub>s2 instance_of\<^sub>l\<^sub>s_trans by blast
  ultimately
  show "falsifies\<^sub>c G (std\<^sub>2 C\<^sub>2)" by auto
next
  assume asm: "falsifies\<^sub>c G (std\<^sub>2 C\<^sub>2)"
  then have inst: "instance_of\<^sub>l\<^sub>s (std\<^sub>2 C\<^sub>2) C\<^sub>2" unfolding instance_of\<^sub>l\<^sub>s_def by auto

  from asm obtain Cg where "instance_of\<^sub>l\<^sub>s Cg (std\<^sub>2 C\<^sub>2)  \<and> falsifies\<^sub>g G Cg" by auto
  moreover
  then have "instance_of\<^sub>l\<^sub>s Cg C\<^sub>2" using inst instance_of\<^sub>l\<^sub>s_trans by blast
  ultimately
  show "falsifies\<^sub>c G C\<^sub>2" by auto
qed

lemma std\<^sub>1_renames: "var_renaming_of C\<^sub>1 (std\<^sub>1 C\<^sub>1)"
proof -
  have "instance_of\<^sub>l\<^sub>s C\<^sub>1 (std\<^sub>1 C\<^sub>1)" using std_apart_instance_of\<^sub>l\<^sub>s1 by auto
  moreover have "instance_of\<^sub>l\<^sub>s (std\<^sub>1 C\<^sub>1) C\<^sub>1" unfolding instance_of\<^sub>l\<^sub>s_def by auto
  ultimately show "var_renaming_of C\<^sub>1 (std\<^sub>1 C\<^sub>1)" unfolding var_renaming_of_def by auto
qed

lemma std\<^sub>2_renames: "var_renaming_of C\<^sub>2 (std\<^sub>2 C\<^sub>2)"
proof -
  have "instance_of\<^sub>l\<^sub>s C\<^sub>2 (std\<^sub>2 C\<^sub>2)" using std_apart_instance_of\<^sub>l\<^sub>s2 by auto
  moreover have "instance_of\<^sub>l\<^sub>s (std\<^sub>2 C\<^sub>2) C\<^sub>2" unfolding instance_of\<^sub>l\<^sub>s_def by auto
  ultimately show "var_renaming_of C\<^sub>2 (std\<^sub>2 C\<^sub>2)" unfolding var_renaming_of_def by auto
qed


section \<open>Semantic Trees\<close>

abbreviation closed_branch :: "partial_pred_denot \<Rightarrow> tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "closed_branch G T Cs \<equiv> branch G T \<and> falsifies\<^sub>c\<^sub>s G Cs"

abbreviation(input) open_branch :: "partial_pred_denot \<Rightarrow> tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "open_branch G T Cs \<equiv> branch G T \<and> \<not>falsifies\<^sub>c\<^sub>s G Cs"

definition closed_tree :: "tree \<Rightarrow> fterm clause set \<Rightarrow> bool" where
  "closed_tree T Cs \<longleftrightarrow> anybranch T (\<lambda>b. closed_branch b T Cs) 
                  \<and> anyinternal T (\<lambda>p. \<not>falsifies\<^sub>c\<^sub>s p Cs)" 


section \<open>Herbrand's Theorem\<close>

lemma maximum:
  assumes asm: "finite C"
  shows "\<exists>n :: nat. \<forall>l \<in> C. f l \<le> n"
proof
  from asm show "\<forall>l\<in>C. f l \<le> (Max (f ` C))" by auto
qed

lemma extend_preserves_model: (* only for ground *)
  assumes f_infpath: "wf_infpath (f :: nat \<Rightarrow> partial_pred_denot)" 
  assumes C_ground: "ground\<^sub>l\<^sub>s C"
  assumes C_sat: "\<not>falsifies\<^sub>c (f (Suc n)) C"
  assumes n_max: "\<forall>l\<in>C. nat_of_fatom (get_atom l) \<le> n"
  shows "eval\<^sub>c HFun (extend f) C"
proof -
  let ?F = "HFun" 
  let ?G = "extend f"
  {
    fix E
    from C_sat have "\<forall>C'. (\<not>instance_of\<^sub>l\<^sub>s C' C \<or> \<not>falsifies\<^sub>g (f (Suc n)) C')" by auto
    then have "\<not>falsifies\<^sub>g (f (Suc n)) C" using instance_of\<^sub>l\<^sub>s_self by auto
    then obtain l where l_p: "l\<in>C \<and> \<not>falsifies\<^sub>l (f (Suc n)) l" using C_ground by blast
    let ?i = "nat_of_fatom (get_atom l)"
     
    from l_p have i_n: "?i \<le> n" using n_max by auto
    then have j_n: "?i < length (f (Suc n))" using f_infpath infpath_length[of f] by auto
      
    have "eval\<^sub>l E HFun (extend f) l"
      proof (cases l)
        case (Pos P ts)
        from Pos l_p C_ground have ts_ground: "ground\<^sub>t\<^sub>s ts" by auto

        have "\<not>falsifies\<^sub>l (f (Suc n)) l" using l_p by auto
        then have "f (Suc n) ! ?i = True" 
          using j_n Pos ts_ground empty_subts[of ts] unfolding falsifies\<^sub>l_def by auto
        moreover have "f (Suc ?i) ! ?i = f (Suc n) ! ?i" 
          using f_infpath i_n j_n infpath_length[of f] ith_in_extension[of f] by simp
        ultimately
        have "f (Suc ?i) ! ?i = True" using Pos by auto
        then have "?G P (hterms_of_fterms ts)" using Pos by (simp add: nat_of_fatom_def) 
        then show ?thesis using eval\<^sub>l_ground\<^sub>t\<^sub>s[of ts _ ?G P] ts_ground Pos by auto
      next
        case (Neg P ts) (* Symmetric *)
        from Neg l_p C_ground have ts_ground: "ground\<^sub>t\<^sub>s ts" by auto

        have "\<not>falsifies\<^sub>l (f (Suc n)) l" using l_p by auto  
        then have "f (Suc n) ! ?i = False" 
          using j_n Neg ts_ground empty_subts[of ts] unfolding falsifies\<^sub>l_def by auto
        moreover have "f (Suc ?i) ! ?i = f (Suc n) ! ?i" 
          using f_infpath i_n j_n infpath_length[of f] ith_in_extension[of f] by simp
        ultimately
        have "f (Suc ?i) ! ?i = False" using Neg by auto
        then have "\<not>?G P (hterms_of_fterms ts)" using Neg by (simp add: nat_of_fatom_def) 
        then show ?thesis using Neg eval\<^sub>l_ground\<^sub>t\<^sub>s[of ts _ ?G P] ts_ground by auto
      qed
    then have "\<exists>l \<in> C. eval\<^sub>l E HFun (extend f) l" using l_p by auto
  }
  then have "eval\<^sub>c HFun (extend f) C" unfolding eval\<^sub>c_def by auto
  then show ?thesis using instance_of\<^sub>l\<^sub>s_self by auto
qed

lemma extend_preserves_model2: (* only for ground *)
  assumes f_infpath: "wf_infpath (f :: nat \<Rightarrow> partial_pred_denot)" 
  assumes C_ground: "ground\<^sub>l\<^sub>s C"
  assumes fin_c: "finite C"
  assumes model_C: "\<forall>n. \<not>falsifies\<^sub>c (f n) C"
  shows C_false: "eval\<^sub>c HFun (extend f) C"
proof -
  \<comment> \<open>Since C is finite, C has a largest index of a literal.\<close>
  obtain n where largest: "\<forall>l \<in> C. nat_of_fatom (get_atom l) \<le> n" using fin_c maximum[of C "\<lambda>l. nat_of_fatom (get_atom l)"] by blast
  moreover
  then have "\<not>falsifies\<^sub>c (f (Suc n)) C" using model_C by auto
  ultimately show ?thesis using model_C f_infpath C_ground extend_preserves_model[of f C n ] by blast
qed

lemma extend_infpath: 
  assumes f_infpath: "wf_infpath (f :: nat \<Rightarrow> partial_pred_denot)"
  assumes model_c: "\<forall>n. \<not>falsifies\<^sub>c (f n) C"
  assumes fin_c: "finite C"
  shows "eval\<^sub>c HFun (extend f) C"
unfolding eval\<^sub>c_def proof 
  fix E
  let ?G = "extend f"
  let ?\<sigma> = "sub_of_denot E"
  
  from fin_c have fin_c\<sigma>: "finite (C \<cdot>\<^sub>l\<^sub>s sub_of_denot E)" by auto
  have groundc\<sigma>: "ground\<^sub>l\<^sub>s (C \<cdot>\<^sub>l\<^sub>s sub_of_denot E)" using sub_of_denot_equiv_ground by auto

  \<comment> \<open>Here starts the proof\<close>
  \<comment> \<open>We go from syntactic FO world to syntactic ground world:\<close>
  from model_c have "\<forall>n. \<not>falsifies\<^sub>c (f n) (C \<cdot>\<^sub>l\<^sub>s ?\<sigma>)" using partial_equiv_subst by blast
  \<comment> \<open>Then from syntactic ground world to semantic ground world:\<close>
  then have "eval\<^sub>c HFun ?G (C \<cdot>\<^sub>l\<^sub>s ?\<sigma>)" using groundc\<sigma> f_infpath fin_c\<sigma> extend_preserves_model2[of f "C \<cdot>\<^sub>l\<^sub>s ?\<sigma>"] by blast
  \<comment> \<open>Then from semantic ground world to semantic FO world:\<close>
  then have "\<forall>E. \<exists>l \<in> (C \<cdot>\<^sub>l\<^sub>s ?\<sigma>). eval\<^sub>l E HFun ?G l" unfolding eval\<^sub>c_def by auto
  then have "\<exists>l \<in> (C \<cdot>\<^sub>l\<^sub>s ?\<sigma>). eval\<^sub>l E HFun ?G l" by auto
  then show "\<exists>l \<in> C. eval\<^sub>l E HFun ?G l" using sub_of_denot_equiv_ground[of C E "extend f"] by blast
qed

text \<open>If we have a infpath of partial models, then we have a model.\<close>
lemma infpath_model:
  assumes f_infpath: "wf_infpath (f :: nat \<Rightarrow> partial_pred_denot)"
  assumes model_cs: "\<forall>n. \<not>falsifies\<^sub>c\<^sub>s (f n) Cs" 
  assumes fin_cs: "finite Cs"
  assumes fin_c: "\<forall>C \<in> Cs. finite C"
  shows "eval\<^sub>c\<^sub>s HFun (extend f) Cs"
proof -
  let ?F = "HFun"
    
  have "\<forall>C \<in> Cs. eval\<^sub>c ?F (extend f) C"  
    proof (rule ballI)
      fix C
      assume asm: "C \<in> Cs"
      then have "\<forall>n. \<not>falsifies\<^sub>c (f n) C" using model_cs by auto
      then show "eval\<^sub>c ?F (extend f) C" using fin_c asm f_infpath extend_infpath[of f C] by auto
    qed                                                                      
  then show "eval\<^sub>c\<^sub>s ?F (extend f) Cs" unfolding eval\<^sub>c\<^sub>s_def by auto
qed

fun deeptree :: "nat \<Rightarrow> tree" where
  "deeptree 0 = Leaf"
| "deeptree (Suc n) = Branching (deeptree n) (deeptree n)"

lemma branch_length: 
  assumes "branch b (deeptree n)"
  shows "length b = n"
using assms proof (induction n arbitrary: b)
  case 0 then show ?case using branch_inv_Leaf by auto
next
  case (Suc n)
  then have "branch b (Branching (deeptree n) (deeptree n))" by auto
  then obtain a b' where p: "b = a#b'\<and> branch b' (deeptree n)" using branch_inv_Branching[of b] by blast
  then have "length b' = n" using Suc by auto
  then show ?case using p by auto
qed

lemma infinity:
  assumes inj: "\<forall>n :: nat. undiago (diago n) = n" 
  assumes all_tree: "\<forall>n :: nat. (diago n) \<in> tree"
  shows "\<not>finite tree"
proof -
  from inj all_tree have "\<forall>n. n = undiago (diago n) \<and> (diago n) \<in> tree" by auto
  then have "\<forall>n. \<exists>ds. n = undiago ds \<and> ds \<in> tree" by auto
  then have "undiago ` tree = (UNIV :: nat set)" by auto
  then have "\<not>finite tree"by (metis finite_imageI infinite_UNIV_nat) 
  then show ?thesis by auto
qed

lemma longer_falsifies\<^sub>l:
  assumes "falsifies\<^sub>l ds l"
  shows "falsifies\<^sub>l (ds@d) l"
proof - 
  let ?i = "nat_of_fatom (get_atom l)"
  from assms have i_p: "ground\<^sub>l l \<and>  ?i < length ds \<and> ds ! ?i = (\<not>sign l)" unfolding falsifies\<^sub>l_def by meson
  moreover
  from i_p have "?i < length (ds@d)" by auto
  moreover
  from i_p have "(ds@d) ! ?i = (\<not>sign l)" by (simp add: nth_append) 
  ultimately
  show ?thesis unfolding falsifies\<^sub>l_def by simp
qed

lemma longer_falsifies\<^sub>g:
  assumes "falsifies\<^sub>g ds C"
  shows "falsifies\<^sub>g (ds @ d) C"
proof -
  {
    fix l
    assume "l\<in>C"
    then have "falsifies\<^sub>l (ds @ d) l" using assms longer_falsifies\<^sub>l by auto
  } then show ?thesis using assms by auto
qed

lemma longer_falsifies\<^sub>c:
  assumes "falsifies\<^sub>c ds C"
  shows "falsifies\<^sub>c (ds @ d) C"
proof -
  from assms obtain C' where "instance_of\<^sub>l\<^sub>s C' C \<and> falsifies\<^sub>g ds C'" by auto
  moreover
  then have "falsifies\<^sub>g (ds @ d) C'" using longer_falsifies\<^sub>g by auto
  ultimately show ?thesis by auto
qed

text \<open>We use this so that we can apply König's lemma.\<close>
lemma longer_falsifies:  
  assumes "falsifies\<^sub>c\<^sub>s ds Cs"
  shows "falsifies\<^sub>c\<^sub>s (ds @ d) Cs"
proof -
  from assms obtain C where "C \<in> Cs \<and> falsifies\<^sub>c ds C" by auto
  moreover
  then have "falsifies\<^sub>c (ds @ d) C" using longer_falsifies\<^sub>c[of C ds d] by blast
  ultimately
  show ?thesis by auto
qed

text \<open>If all finite semantic trees have an open branch, then the set of clauses has a model.\<close>
theorem herbrand':
  assumes openb: "\<forall>T. \<exists>G. open_branch G T Cs"
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  shows "\<exists>G. eval\<^sub>c\<^sub>s HFun G Cs"
proof -
  \<comment> \<open>Show T infinite:\<close>
  let ?tree = "{G. \<not>falsifies\<^sub>c\<^sub>s G Cs}"
  let ?undiag = length
  let ?diag = "(\<lambda>l. SOME b. open_branch b (deeptree l) Cs) :: nat \<Rightarrow> partial_pred_denot"

  from openb have diag_open: "\<forall>l. open_branch (?diag l) (deeptree l) Cs"
    using someI_ex[of "\<lambda>b. open_branch b (deeptree _) Cs"] by auto
  then have "\<forall>n. ?undiag (?diag n) = n" using branch_length by auto
  moreover
  have "\<forall>n. (?diag n) \<in> ?tree" using diag_open by auto
  ultimately
  have "\<not>finite ?tree" using infinity[of _ "\<lambda>n. SOME b. open_branch b (_ n) Cs"] by simp
  \<comment> \<open>Get infinite path:\<close>
  moreover 
  have "\<forall>ds d. \<not>falsifies\<^sub>c\<^sub>s (ds @ d) Cs \<longrightarrow> \<not>falsifies\<^sub>c\<^sub>s ds Cs" 
    using longer_falsifies[of Cs] by blast
  then have "(\<forall>ds d. ds @ d \<in> ?tree \<longrightarrow> ds \<in> ?tree)" by auto
  ultimately
  have "\<exists>c. wf_infpath c \<and> (\<forall>n. c n \<in> ?tree)" using konig[of ?tree] by blast
  then have "\<exists>G. wf_infpath G \<and> (\<forall>n. \<not> falsifies\<^sub>c\<^sub>s (G n) Cs)" by auto
  \<comment> \<open>Apply above infpath lemma:\<close>
  then show "\<exists>G. eval\<^sub>c\<^sub>s HFun G Cs" using infpath_model finite_cs by auto
qed

lemma shorter_falsifies\<^sub>l:
  assumes "falsifies\<^sub>l (ds@d) l"
  assumes "nat_of_fatom (get_atom l) < length ds"
  shows "falsifies\<^sub>l ds l"
proof -
  let ?i = "nat_of_fatom (get_atom l)"
  from assms have i_p: "ground\<^sub>l l \<and>  ?i < length (ds@d) \<and> (ds@d) ! ?i = (\<not>sign l)" unfolding falsifies\<^sub>l_def by meson
  moreover
  then have "?i < length ds" using assms by auto
  moreover
  then have "ds ! ?i = (\<not>sign l)" using i_p nth_append[of ds d ?i] by auto
  ultimately show ?thesis using assms unfolding falsifies\<^sub>l_def by simp
qed

theorem herbrand'_contra:
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  assumes unsat: "\<forall>G. \<not>eval\<^sub>c\<^sub>s HFun G Cs"
  shows "\<exists>T. \<forall>G. branch G T \<longrightarrow> closed_branch G T Cs"
proof -
  from finite_cs unsat have "(\<forall>T. \<exists>G. open_branch G T Cs) \<longrightarrow> (\<exists>G. eval\<^sub>c\<^sub>s HFun G Cs)" using herbrand' by blast
  then show ?thesis using unsat by blast 
qed

theorem herbrand:
  assumes unsat: "\<forall>G. \<not>eval\<^sub>c\<^sub>s HFun G Cs"
  assumes finite_cs: "finite Cs" "\<forall>C\<in>Cs. finite C"
  shows "\<exists>T. closed_tree T Cs"
proof -
  from unsat finite_cs obtain T where "anybranch T (\<lambda>b. closed_branch b T Cs)" using herbrand'_contra[of Cs] by blast
  then have "\<exists>T. anybranch T (\<lambda>p. falsifies\<^sub>c\<^sub>s p Cs) \<and> anyinternal T (\<lambda>p. \<not> falsifies\<^sub>c\<^sub>s p Cs)" 
    using cutoff_branch_internal[of T "\<lambda>p. falsifies\<^sub>c\<^sub>s p Cs"] by blast
  then show ?thesis unfolding closed_tree_def by auto
qed

end
