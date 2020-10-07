section \<open>Exception Monad for Refine-Monadic\<close>
theory Exc_Nres_Monad
imports "Refine_Monadic.Refine_Monadic" DRAT_Misc
begin

(*
  TODO:
    * Integrate with sepref --- currently, it's "integrated" by providing 
        some support to translate the program in to a plain nres monad before 
        sepref is invoked.
    * Move to Refine_Monadic.
*)
  
declare TrueI[refine_vcg]

type_synonym ('e,'a) enres = "('e + 'a) nres"

named_theorems enres_unfolds \<open>Unfolding theorems from enres to nres\<close>


definition [enres_unfolds]: "ERETURN x \<equiv> RETURN (Inr x)"
definition ebind :: "('e,'a) enres \<Rightarrow> ('a \<Rightarrow> ('e,'b) enres) \<Rightarrow> ('e,'b) enres" 
  where [enres_unfolds]:
  "ebind m f \<equiv> do {
    x \<leftarrow> m;
    case x of Inl e \<Rightarrow> RETURN (Inl e) | Inr x \<Rightarrow> f x
  }"
definition [enres_unfolds]: "THROW e == RETURN (Inl e)"

definition [enres_unfolds]: "ESPEC \<Phi> \<Psi> \<equiv> SPEC (\<lambda>Inl e \<Rightarrow> \<Phi> e | Inr r \<Rightarrow> \<Psi> r)"

definition [enres_unfolds]: "CATCH m h \<equiv> do { r\<leftarrow>m; case r of Inl e \<Rightarrow> h e | Inr r \<Rightarrow> RETURN (Inr r) }"



abbreviation (do_notation) bind_doE where "bind_doE \<equiv> ebind"

notation (output) bind_doE (infixr "\<bind>" 54)
notation (ASCII output) bind_doE (infixr ">>=" 54)


nonterminal doE_binds and doE_bind
syntax
  "_doE_block" :: "doE_binds \<Rightarrow> 'a" ("doE {//(2  _)//}" [12] 62)
  "_doE_bind"  :: "[pttrn, 'a] \<Rightarrow> doE_bind" ("(2_ \<leftarrow>/ _)" 13)
  "_doE_let" :: "[pttrn, 'a] \<Rightarrow> doE_bind" ("(2let _ =/ _)" [1000, 13] 13)
  "_doE_then" :: "'a \<Rightarrow> doE_bind" ("_" [14] 13)
  "_doE_final" :: "'a \<Rightarrow> doE_binds" ("_")
  "_doE_cons" :: "[doE_bind, doE_binds] \<Rightarrow> doE_binds" ("_;//_" [13, 12] 12)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr "\<then>" 54)

syntax (ASCII)
  "_doE_bind" :: "[pttrn, 'a] \<Rightarrow> doE_bind" ("(2_ <-/ _)" 13)
  "_thenM" :: "['a, 'b] \<Rightarrow> 'c" (infixr ">>" 54)

translations
  "_doE_block (_doE_cons (_doE_then t) (_doE_final e))"
    \<rightleftharpoons> "CONST bind_doE t (\<lambda>_. e)"
  "_doE_block (_doE_cons (_doE_bind p t) (_doE_final e))"
    \<rightleftharpoons> "CONST bind_doE t (\<lambda>p. e)"
  "_doE_block (_doE_cons (_doE_let p t) bs)"
    \<rightleftharpoons> "let p = t in _doE_block bs"
  "_doE_block (_doE_cons b (_doE_cons c cs))"
    \<rightleftharpoons> "_doE_block (_doE_cons b (_doE_final (_doE_block (_doE_cons c cs))))"
  "_doE_cons (_doE_let p t) (_doE_final s)"
    \<rightleftharpoons> "_doE_final (let p = t in s)"
  "_doE_block (_doE_final e)" \<rightharpoonup> "e"
  "(m \<then> n)" \<rightharpoonup> "(m \<bind> (\<lambda>_. n))"


definition [enres_unfolds]: "CHECK \<Phi> e \<equiv> if \<Phi> then ERETURN () else THROW e"

definition [enres_unfolds]: "EASSUME \<Phi> \<equiv> if \<Phi> then ERETURN () else SUCCEED"
definition [enres_unfolds]: "EASSERT \<Phi> \<equiv> if \<Phi> then ERETURN () else FAIL"

lemma EASSUME_simps[simp]: 
  "EASSUME True = ERETURN ()"
  "EASSUME False = SUCCEED"
  unfolding EASSUME_def by auto

lemma EASSERT_simps[simp]: 
  "EASSERT True = ERETURN ()"
  "EASSERT False = FAIL"
  unfolding EASSERT_def by auto

lemma CHECK_simps[simp]: 
  "CHECK True e = ERETURN ()" 
  "CHECK False e = THROW e" 
  unfolding CHECK_def by auto

lemma pw_ESPEC[simp, refine_pw_simps]:
  "nofail (ESPEC \<Phi> \<Psi>)"
  "inres (ESPEC \<Phi> \<Psi>) (Inl e) \<longleftrightarrow> \<Phi> e"
  "inres (ESPEC \<Phi> \<Psi>) (Inr x) \<longleftrightarrow> \<Psi> x"
  unfolding enres_unfolds
  by auto

lemma pw_ERETURN[simp, refine_pw_simps]:
  "nofail (ERETURN x)"
  "\<not>inres (ERETURN x) (Inl e)"
  "inres (ERETURN x) (Inr y) \<longleftrightarrow> x=y"
  unfolding enres_unfolds
  by auto

lemma pw_ebind[refine_pw_simps]:
  "nofail (ebind m f) \<longleftrightarrow> nofail m \<and> (\<forall>x. inres m (Inr x) \<longrightarrow> nofail (f x))"
  "inres (ebind m f) (Inl e) \<longleftrightarrow> inres m (Inl e) \<or> (\<exists>x. inres m (Inr x) \<and> inres (f x) (Inl e))"
  "inres (ebind m f) (Inr x) \<longleftrightarrow> nofail m \<longrightarrow> (\<exists>y. inres m (Inr y) \<and> inres (f y) (Inr x))"
  unfolding enres_unfolds
  apply (auto simp: refine_pw_simps split: sum.split)
  using sum.exhaust_sel apply blast
  using sum.exhaust_sel apply blast
  done

lemma pw_THROW[simp,refine_pw_simps]:
  "nofail (THROW e)"
  "inres (THROW e) (Inl f) \<longleftrightarrow> f=e"
  "\<not>inres (THROW e) (Inr x)"
  unfolding enres_unfolds
  by (auto simp: refine_pw_simps)

lemma pw_CHECK[simp, refine_pw_simps]:
  "nofail (CHECK \<Phi> e)"
  "inres (CHECK \<Phi> e) (Inl f) \<longleftrightarrow> \<not>\<Phi> \<and> f=e"
  "inres (CHECK \<Phi> e) (Inr u) \<longleftrightarrow> \<Phi>"
  unfolding enres_unfolds
  by (auto simp: refine_pw_simps)
  
lemma pw_EASSUME[simp, refine_pw_simps]:
  "nofail (EASSUME \<Phi>)"
  "\<not>inres (EASSUME \<Phi>) (Inl e)"
  "inres (EASSUME \<Phi>) (Inr u) \<longleftrightarrow> \<Phi>"
  unfolding EASSUME_def  
  by (auto simp: refine_pw_simps)

lemma pw_EASSERT[simp, refine_pw_simps]:
  "nofail (EASSERT \<Phi>) \<longleftrightarrow> \<Phi>"
  "inres (EASSERT \<Phi>) (Inr u)"
  "inres (EASSERT \<Phi>) (Inl e) \<longleftrightarrow> \<not>\<Phi>"
  unfolding EASSERT_def  
  by (auto simp: refine_pw_simps)

lemma pw_CATCH[refine_pw_simps]:
  "nofail (CATCH m h) \<longleftrightarrow> (nofail m \<and> (\<forall>x. inres m (Inl x) \<longrightarrow> nofail (h x)))"
  "inres (CATCH m h) (Inl e) \<longleftrightarrow> (nofail m \<longrightarrow> (\<exists>e'. inres m (Inl e') \<and> inres (h e') (Inl e)))"
  "inres (CATCH m h) (Inr x) \<longleftrightarrow> inres m (Inr x) \<or> (\<exists>e. inres m (Inl e) \<and> inres (h e) (Inr x))"
  unfolding CATCH_def
  apply (auto simp add: refine_pw_simps split: sum.splits)  
  using sum.exhaust_sel apply blast
  using sum.exhaust_sel apply blast
  done
  
lemma pw_ele_iff: "m \<le> n \<longleftrightarrow> (nofail n \<longrightarrow> 
    nofail m 
  \<and> (\<forall>e. inres m (Inl e) \<longrightarrow> inres n (Inl e))
  \<and> (\<forall>x. inres m (Inr x) \<longrightarrow> inres n (Inr x))
  )"
  apply (auto simp: pw_le_iff)
  by (metis sum.exhaust_sel)

lemma pw_eeq_iff: "m = n \<longleftrightarrow> 
    (nofail m \<longleftrightarrow> nofail n) 
  \<and> (\<forall>e. inres m (Inl e) \<longleftrightarrow> inres n (Inl e))
  \<and> (\<forall>x. inres m (Inr x) \<longleftrightarrow> inres n (Inr x))"
  apply (auto simp: pw_eq_iff)
  by (metis sum.exhaust_sel)+
  


lemma enres_monad_laws[simp]:
  "ebind (ERETURN x) f = f x"
  "ebind m (ERETURN) = m"
  "ebind (ebind m f) g = ebind m (\<lambda>x. ebind (f x) g)"
  by (auto simp: pw_eeq_iff refine_pw_simps)
  
lemma enres_additional_laws[simp]:
  "ebind (THROW e) f = THROW e"
  
  "CATCH (THROW e) h = h e"
  "CATCH (ERETURN x) h = ERETURN x"
  "CATCH m THROW = m"
  
  apply (auto simp: pw_eeq_iff refine_pw_simps)
  done  

lemmas ESPEC_trans = order_trans[where z="ESPEC Error_Postcond Normal_Postcond" for Error_Postcond Normal_Postcond, zero_var_indexes]

lemma ESPEC_cons: 
  assumes "m \<le> ESPEC E Q"
  assumes "\<And>e. E e \<Longrightarrow> E' e"
  assumes "\<And>x. Q x \<Longrightarrow> Q' x"
  shows "m \<le> ESPEC E' Q'"  
  using assms by (auto simp: pw_ele_iff)
  
  
lemma ebind_rule_iff: "doE { x\<leftarrow>m; f x } \<le> ESPEC \<Phi> \<Psi> \<longleftrightarrow> m \<le> ESPEC \<Phi> (\<lambda>x. f x \<le> ESPEC \<Phi> \<Psi>)"
  by (auto simp: pw_ele_iff refine_pw_simps)

lemmas ebind_rule[refine_vcg] = ebind_rule_iff[THEN iffD2]

lemma ERETURN_rule_iff[simp]: "ERETURN x \<le> ESPEC \<Phi> \<Psi> \<longleftrightarrow> \<Psi> x"
  by (auto simp: pw_ele_iff refine_pw_simps)
lemmas ERETURN_rule[refine_vcg] = ERETURN_rule_iff[THEN iffD2]

lemma ESPEC_rule_iff: "ESPEC \<Phi> \<Psi> \<le> ESPEC \<Phi>' \<Psi>' \<longleftrightarrow> (\<forall>e. \<Phi> e \<longrightarrow> \<Phi>' e) \<and> (\<forall>x. \<Psi> x \<longrightarrow> \<Psi>' x)"
  by (auto simp: pw_ele_iff refine_pw_simps)
lemmas ESPEC_rule[refine_vcg] = ESPEC_rule_iff[THEN iffD2]

lemma THROW_rule_iff: "THROW e \<le> ESPEC \<Phi> \<Psi> \<longleftrightarrow> \<Phi> e"
  by (auto simp: pw_ele_iff refine_pw_simps)
lemmas THROW_rule[refine_vcg] = THROW_rule_iff[THEN iffD2]

lemma CATCH_rule_iff: "CATCH m h \<le> ESPEC \<Phi> \<Psi> \<longleftrightarrow> m \<le> ESPEC (\<lambda>e. h e \<le> ESPEC \<Phi> \<Psi>) \<Psi>"
  by (auto simp: pw_ele_iff refine_pw_simps)
lemmas CATCH_rule[refine_vcg] = CATCH_rule_iff[THEN iffD2]



lemma CHECK_rule_iff: "CHECK c e \<le> ESPEC \<Phi> \<Psi> \<longleftrightarrow> (c \<longrightarrow> \<Psi> ()) \<and> (\<not>c \<longrightarrow> \<Phi> e)"
  by (auto simp: pw_ele_iff refine_pw_simps)

lemma CHECK_rule[refine_vcg]:
  assumes "c \<Longrightarrow> \<Psi> ()"
  assumes "\<not>c \<Longrightarrow> \<Phi> e"
  shows "CHECK c e \<le> ESPEC \<Phi> \<Psi>"
  using assms by (simp add: CHECK_rule_iff)



lemma EASSUME_rule[refine_vcg]: "\<lbrakk>\<Phi> \<Longrightarrow> \<Psi> ()\<rbrakk> \<Longrightarrow> EASSUME \<Phi> \<le> ESPEC E \<Psi>"
  by (cases \<Phi>) auto

lemma EASSERT_rule[refine_vcg]: "\<lbrakk>\<Phi>; \<Phi> \<Longrightarrow> \<Psi> ()\<rbrakk> \<Longrightarrow> EASSERT \<Phi> \<le> ESPEC E \<Psi>" by auto

lemma eprod_rule[refine_vcg]: 
  "\<lbrakk>\<And>a b. p=(a,b) \<Longrightarrow> S a b \<le> ESPEC \<Phi> \<Psi>\<rbrakk> \<Longrightarrow> (case p of (a,b) \<Rightarrow> S a b) \<le> ESPEC \<Phi> \<Psi>"
  by (auto split: prod.split)

(* TODO: Add a simplifier setup that normalizes nested case-expressions to
  the vcg! *)
lemma eprod2_rule[refine_vcg]:
  assumes "\<And>a b c d. \<lbrakk>ab=(a,b); cd=(c,d)\<rbrakk> \<Longrightarrow> f a b c d \<le> ESPEC \<Phi> \<Psi>"
  shows "(\<lambda>(a,b) (c,d). f a b c d) ab cd \<le> ESPEC \<Phi> \<Psi>"
  using assms
  by (auto split: prod.split)

lemma eif_rule[refine_vcg]: 
  "\<lbrakk> b \<Longrightarrow> S1 \<le> ESPEC \<Phi> \<Psi>; \<not>b \<Longrightarrow> S2 \<le> ESPEC \<Phi> \<Psi>\<rbrakk> 
  \<Longrightarrow> (if b then S1 else S2) \<le> ESPEC \<Phi> \<Psi>"
  by (auto)

lemma eoption_rule[refine_vcg]: 
  "\<lbrakk> v=None \<Longrightarrow> S1 \<le> ESPEC \<Phi> \<Psi>; \<And>x. v=Some x \<Longrightarrow> f2 x \<le> ESPEC \<Phi> \<Psi>\<rbrakk> 
  \<Longrightarrow> case_option S1 f2 v \<le> ESPEC \<Phi> \<Psi>"
  by (auto split: option.split)

lemma eLet_rule[refine_vcg]: "f v \<le> ESPEC \<Phi> \<Psi> \<Longrightarrow> (let x=v in f x) \<le> ESPEC \<Phi> \<Psi>" by simp

lemma eLet_rule':
  assumes "\<And>x. x=v \<Longrightarrow> f x \<le> ESPEC \<Phi> \<Psi>"
  shows "Let v (\<lambda>x. f x) \<le> ESPEC \<Phi> \<Psi>"
  using assms by simp

definition [enres_unfolds]: "EWHILEIT I c f s \<equiv> WHILEIT 
  (\<lambda>Inl _ \<Rightarrow> True | Inr s \<Rightarrow> I s) 
  (\<lambda>Inl _ \<Rightarrow> False | Inr s \<Rightarrow> c s)
  (\<lambda>s. ASSERT (\<not>isl s) \<then> (let s = projr s in f s))
  (Inr s)"

definition [enres_unfolds]: "EWHILET \<equiv> EWHILEIT (\<lambda>_. True)"

lemma EWHILEIT_rule[refine_vcg]:
  assumes WF: "wf R"
    and I0: "I s\<^sub>0"
    and IS: "\<And>s. \<lbrakk>I s; b s; (s,s\<^sub>0)\<in>R\<^sup>*\<rbrakk> \<Longrightarrow> f s \<le> ESPEC E (\<lambda>s'. I s' \<and> (s', s) \<in> R)"
    and IMP: "\<And>s. \<lbrakk>I s; \<not> b s; (s,s\<^sub>0)\<in>R\<^sup>*\<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "EWHILEIT I b f s\<^sub>0 \<le> ESPEC E \<Phi>"
  unfolding EWHILEIT_def ESPEC_def
  apply (rule order_trans[OF WHILEIT_weaken[where I="\<lambda>Inl e \<Rightarrow> E e | Inr s \<Rightarrow> I s \<and> (s,s\<^sub>0)\<in>R\<^sup>*"]])
  apply (auto split: sum.splits) []
  apply (rule WHILEIT_rule[where R="inv_image (less_than <*lex*> R) (\<lambda>Inl e \<Rightarrow> (0,undefined) | Inr s \<Rightarrow> (1,s))"])
  subgoal using WF by auto
  subgoal using I0 by auto
  subgoal 
    apply (clarsimp split: sum.splits simp: ESPEC_def)
    apply (rule order_trans[OF IS])
    apply (auto simp: ESPEC_def)
    done
  subgoal using IMP by (auto split: sum.splits)
  done
  
lemma EWHILET_rule:
  assumes WF: "wf R"
    and I0: "I s\<^sub>0"
    and IS: "\<And>s. \<lbrakk>I s; b s; (s,s\<^sub>0)\<in>R\<^sup>*\<rbrakk> \<Longrightarrow> f s \<le> ESPEC E (\<lambda>s'. I s' \<and> (s', s) \<in> R)"
    and IMP: "\<And>s. \<lbrakk>I s; \<not> b s; (s,s\<^sub>0)\<in>R\<^sup>*\<rbrakk> \<Longrightarrow> \<Phi> s"
  shows "EWHILET b f s\<^sub>0 \<le> ESPEC E \<Phi>"
  unfolding EWHILET_def EWHILEIT_def ESPEC_def
  apply (rule order_trans[OF WHILEIT_weaken[where I="\<lambda>Inl e \<Rightarrow> E e | Inr s \<Rightarrow> I s \<and> (s,s\<^sub>0)\<in>R\<^sup>*"]])
  apply (auto split: sum.splits) []
  apply (rule WHILEIT_rule[where R="inv_image (less_than <*lex*> R) (\<lambda>Inl e \<Rightarrow> (0,undefined) | Inr s \<Rightarrow> (1,s))"])
  subgoal using WF by auto
  subgoal using I0 by auto
  subgoal 
    apply (clarsimp split: sum.splits simp: ESPEC_def)
    apply (rule order_trans[OF IS])
    apply (auto simp: ESPEC_def)
    done
  subgoal using IMP by (auto split: sum.splits)
  done
  
lemma EWHILEIT_weaken:
  assumes "\<And>x. I x \<Longrightarrow> I' x"
  shows "EWHILEIT I' b f x \<le> EWHILEIT I b f x"
  unfolding enres_unfolds
  apply (rule WHILEIT_weaken)
  using assms by (auto split: sum.split)
    
text \<open>Explicitly specify a different invariant. \<close>    
lemma EWHILEIT_expinv_rule:
  assumes WF: "wf R"
    and I0: "I s\<^sub>0"
    and IS: "\<And>s. \<lbrakk>I s; b s; (s,s\<^sub>0)\<in>R\<^sup>*\<rbrakk> \<Longrightarrow> f s \<le> ESPEC E (\<lambda>s'. I s' \<and> (s', s) \<in> R)"
    and IMP: "\<And>s. \<lbrakk>I s; \<not> b s; (s,s\<^sub>0)\<in>R\<^sup>*\<rbrakk> \<Longrightarrow> \<Phi> s"
    and INVIMP: "\<And>s. I s \<Longrightarrow> I' s"
  shows "EWHILEIT I' b f s\<^sub>0 \<le> ESPEC E \<Phi>"
  apply (rule order_trans[OF EWHILEIT_weaken])
  using INVIMP apply assumption
  apply (rule EWHILEIT_rule; fact+)
  done
  

definition [enres_unfolds]: "enfoldli l c f s \<equiv> 
  nfoldli l (\<lambda>Inl e\<Rightarrow>False | Inr x \<Rightarrow> c x) (\<lambda>x s. do {ASSERT (\<not>isl s); let s=projr s; f x s}) (Inr s)"

lemma enfoldli_simps[simp]:
  "enfoldli [] c f s = ERETURN s"
  "enfoldli (x#ls) c f s = 
    (if c s then doE { s\<leftarrow>f x s; enfoldli ls c f s} else ERETURN s)"
  unfolding enres_unfolds
  by (auto split: sum.split intro!: arg_cong[where f = "Refine_Basic.bind _"] ext)

lemma enfoldli_rule:
  assumes I0: "I [] l0 \<sigma>0"
  assumes IS: "\<And>x l1 l2 \<sigma>. \<lbrakk> l0=l1@x#l2; I l1 (x#l2) \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> f x \<sigma> \<le> ESPEC E (I (l1@[x]) l2)"
  assumes FNC: "\<And>l1 l2 \<sigma>. \<lbrakk> l0=l1@l2; I l1 l2 \<sigma>; \<not>c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  assumes FC: "\<And>\<sigma>. \<lbrakk> I l0 [] \<sigma>; c \<sigma> \<rbrakk> \<Longrightarrow> P \<sigma>"
  shows "enfoldli l0 c f \<sigma>0 \<le> ESPEC E P"
  unfolding enfoldli_def ESPEC_def
  apply (rule nfoldli_rule[where I="\<lambda>l1 l2. \<lambda>Inl e \<Rightarrow> E e | Inr \<sigma> \<Rightarrow> I l1 l2 \<sigma>"])
  subgoal by (auto simp: I0)
  subgoal 
    apply (simp split: sum.splits)
    apply (erule (2) order_trans[OF IS])
    apply (auto simp: ESPEC_def)
    done
  subgoal using FNC by (auto split: sum.split)
  subgoal using FC by (auto split: sum.split)
  done


    
    
    
subsection \<open>Data Refinement\<close>

lemma sum_rel_conv:
  "(Inl l, s') \<in> \<langle>L,R\<rangle>sum_rel \<longleftrightarrow> (\<exists>l'. s'=Inl l' \<and> (l,l')\<in>L)"
  "(Inr r, s') \<in> \<langle>L,R\<rangle>sum_rel \<longleftrightarrow> (\<exists>r'. s'=Inr r' \<and> (r,r')\<in>R)"
  "(s, Inl l') \<in> \<langle>L,R\<rangle>sum_rel \<longleftrightarrow> (\<exists>l. s=Inl l \<and> (l,l')\<in>L)"
  "(s, Inr r') \<in> \<langle>L,R\<rangle>sum_rel \<longleftrightarrow> (\<exists>r. s=Inr r \<and> (r,r')\<in>R)"
  "(\<forall>l. s \<noteq> Inl l) \<longleftrightarrow> (\<exists>r. s=Inr r)"
  "(\<forall>r. s \<noteq> Inr r) \<longleftrightarrow> (\<exists>l. s=Inl l)"
  apply -
  subgoal by (cases s'; auto)
  subgoal by (cases s'; auto)
  subgoal by (cases s; auto)
  subgoal by (cases s; auto)
  subgoal by (cases s; auto)
  subgoal by (cases s; auto)
  done  

definition econc_fun ("\<Down>\<^sub>E") where [enres_unfolds]: "econc_fun E R \<equiv> \<Down>(\<langle>E,R\<rangle>sum_rel)"

lemma RELATES_pat_erefine[refine_dref_pattern]: "\<lbrakk>RELATES R; mi \<le>\<Down>\<^sub>E E R m \<rbrakk> \<Longrightarrow> mi \<le>\<Down>\<^sub>E E R m" .

lemma pw_econc_iff[refine_pw_simps]:
  "inres (\<Down>\<^sub>E E R m) (Inl ei) \<longleftrightarrow> (nofail m \<longrightarrow> (\<exists>e. inres m (Inl e) \<and> (ei,e)\<in>E))"
  "inres (\<Down>\<^sub>E E R m) (Inr xi) \<longleftrightarrow> (nofail m \<longrightarrow> (\<exists>x. inres m (Inr x) \<and> (xi,x)\<in>R))"
  "nofail (\<Down>\<^sub>E E R m) \<longleftrightarrow> nofail m"
  by (auto simp: refine_pw_simps econc_fun_def sum_rel_conv)

lemma econc_fun_id[simp]: "\<Down>\<^sub>E Id Id = (\<lambda>x. x)"
  by (auto simp: pw_eeq_iff refine_pw_simps intro!: ext)

lemma econc_fun_ESPEC: "\<Down>\<^sub>E E R (ESPEC \<Phi> \<Psi>) = ESPEC (\<lambda>ei. \<exists>e. (ei,e)\<in>E \<and> \<Phi> e) (\<lambda>ri. \<exists>r. (ri,r)\<in>R \<and> \<Psi> r)"
  by (auto simp: pw_eeq_iff refine_pw_simps)

lemma econc_fun_ERETURN: "\<Down>\<^sub>E E R (ERETURN x) = ESPEC (\<lambda>_. False) (\<lambda>xi. (xi,x)\<in>R)"
  by (auto simp: pw_eeq_iff refine_pw_simps)

lemma econc_fun_univ_id[simp]: "\<Down>\<^sub>E UNIV Id (ESPEC \<Phi> \<Psi>) = ESPEC (\<lambda>_. Ex \<Phi>) \<Psi>"
  by (auto simp: pw_eeq_iff refine_pw_simps)

lemma erefine_same_sup_Id[simp]: "\<lbrakk> Id\<subseteq>E; Id\<subseteq>R \<rbrakk> \<Longrightarrow> m \<le>\<Down>\<^sub>E E R m" by (auto simp: pw_ele_iff refine_pw_simps)

lemma econc_mono3: "m\<le>m' \<Longrightarrow> \<Down>\<^sub>E E R m \<le> \<Down>\<^sub>E E R m'"
  by (auto simp: pw_ele_iff refine_pw_simps)

(* Order of these two is important! *)    
lemma econc_x_trans[trans]: 
  "x \<le> \<Down>\<^sub>E E R y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> \<Down>\<^sub>E E R z"
  by (force simp: pw_ele_iff refine_pw_simps)
lemma econc_econc_trans[trans]: 
  "x \<le>\<Down>\<^sub>E E1 R1 y \<Longrightarrow> y \<le> \<Down>\<^sub>E E2 R2 z \<Longrightarrow> x \<le> \<Down>\<^sub>E (E1 O E2) (R1 O R2) z"    
  by (force simp: pw_ele_iff refine_pw_simps)
  
    
    
lemma ERETURN_refine[refine]: 
  assumes "(xi,x)\<in>R"
  shows "ERETURN xi \<le> \<Down>\<^sub>EE R (ERETURN x)"
  using assms
  by (auto simp: pw_ele_iff refine_pw_simps)

lemma EASSERT_bind_refine_right:
  assumes "\<Phi> \<Longrightarrow> mi \<le>\<Down>\<^sub>E E R m"
  shows "mi \<le>\<Down>\<^sub>E E R (doE {EASSERT \<Phi>; m})"
  using assms
  by (simp add: pw_ele_iff refine_pw_simps)
  
lemma EASSERT_bind_refine_left:
  assumes "\<Phi>"
  assumes "mi \<le>\<Down>\<^sub>E E R m"
  shows "(doE {EASSERT \<Phi>; mi}) \<le>\<Down>\<^sub>E E R m"
  using assms
  by simp

lemma EASSUME_bind_refine_right:
  assumes "\<Phi>"
  assumes "mi \<le>\<Down>\<^sub>E E R m"
  shows "mi \<le>\<Down>\<^sub>E E R (doE {EASSUME \<Phi>; m})"
  using assms
  by (simp)

lemma EASSUME_bind_refine_left:
  assumes "\<Phi> \<Longrightarrow> mi \<le>\<Down>\<^sub>E E R m"
  shows "(doE {EASSUME \<Phi>; mi}) \<le>\<Down>\<^sub>E E R m"
  using assms
  by (simp add: pw_ele_iff refine_pw_simps)

lemma ebind_refine:
  assumes "mi \<le>\<Down>\<^sub>E E R' m"
  assumes "\<And>xi x. (xi,x)\<in>R' \<Longrightarrow> fi xi \<le>\<Down>\<^sub>E E R (f x)"
  shows "doE { xi \<leftarrow> mi; fi xi } \<le> \<Down>\<^sub>E E R (doE { x \<leftarrow> m; f x })"
  using assms
  by (simp add: pw_ele_iff refine_pw_simps) blast

text \<open>Order of this lemmas matters!\<close>
lemmas [refine] = 
  ebind_refine
  EASSERT_bind_refine_left EASSUME_bind_refine_right
  EASSUME_bind_refine_left EASSERT_bind_refine_right

thm refine(1-10)

lemma ebind_refine':
  assumes "mi \<le>\<Down>\<^sub>E E R' m"
  assumes "\<And>xi x. \<lbrakk>(xi,x)\<in>R'; inres mi (Inr xi); inres m (Inr x); nofail mi; nofail m\<rbrakk> \<Longrightarrow> fi xi \<le>\<Down>\<^sub>E E R (f x)"
  shows "doE { xi \<leftarrow> mi; fi xi } \<le> \<Down>\<^sub>E E R (doE { x \<leftarrow> m; f x })"
  using assms
  by (simp add: pw_ele_iff refine_pw_simps) blast

lemma THROW_refine[refine]: "(ei,e)\<in>E \<Longrightarrow> THROW ei \<le>\<Down>\<^sub>E E R (THROW e)"
  by (auto simp: pw_ele_iff refine_pw_simps)

lemma CATCH_refine':
  assumes "mi \<le> \<Down>\<^sub>E E' R m"
  assumes "\<And>ei e. \<lbrakk> (ei,e)\<in>E'; inres mi (Inl ei); inres m (Inl e); nofail mi; nofail m \<rbrakk> \<Longrightarrow> hi ei \<le>\<Down>\<^sub>E E R (h e)"
  shows "CATCH mi hi \<le> \<Down>\<^sub>E E R (CATCH m h)"  
  using assms
  by (simp add: pw_ele_iff refine_pw_simps) blast
  
lemma CATCH_refine[refine]:
  assumes "mi \<le> \<Down>\<^sub>E E' R m"
  assumes "\<And>ei e. \<lbrakk> (ei,e)\<in>E' \<rbrakk> \<Longrightarrow> hi ei \<le>\<Down>\<^sub>E E R (h e)"
  shows "CATCH mi hi \<le> \<Down>\<^sub>E E R (CATCH m h)"  
  using assms CATCH_refine' by metis

lemma CHECK_refine[refine]: 
  assumes "\<Phi>i \<longleftrightarrow> \<Phi>"
  assumes "\<not>\<Phi> \<Longrightarrow> (msgi,msg)\<in>E"
  shows "CHECK \<Phi>i msgi \<le>\<Down>\<^sub>E E Id (CHECK \<Phi> msg)"
  using assms by (auto simp: pw_ele_iff refine_pw_simps)

text \<open>This must be declared after @{thm CHECK_refine}!\<close>
lemma CHECK_bind_refine[refine]: 
  assumes "\<Phi>i \<longleftrightarrow> \<Phi>"
  assumes "\<not>\<Phi> \<Longrightarrow> (msgi,msg)\<in>E"
  assumes "\<Phi> \<Longrightarrow> mi \<le>\<Down>\<^sub>E E R m"
  shows "doE {CHECK \<Phi>i msgi;mi} \<le>\<Down>\<^sub>E E R (doE {CHECK \<Phi> msg; m})"
  using assms by (auto simp: pw_ele_iff refine_pw_simps)
    
lemma Let_unfold_refine[refine]:
  assumes "f x \<le> \<Down>\<^sub>E E R (f' x')"
  shows "Let x f \<le> \<Down>\<^sub>E E R (Let x' f')"
  using assms by auto

lemma Let_refine:
  assumes "(m,m')\<in>R'"
  assumes "\<And>x x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>\<^sub>E E R (f' x')"
  shows "Let m (\<lambda>x. f x) \<le>\<Down>\<^sub>E E R (Let m' (\<lambda>x'. f' x'))"
  using assms by auto

lemma eif_refine[refine]:
  assumes "(b,b')\<in>bool_rel"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> S1 \<le> \<Down>\<^sub>E E R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> S2 \<le> \<Down>\<^sub>E E R S2'"
  shows "(if b then S1 else S2) \<le> \<Down>\<^sub>E E R (if b' then S1' else S2')"
  using assms by auto




(* TODO: Also add enfoldli_invar_refine *)
lemma enfoldli_refine[refine]:
  assumes "(li, l) \<in> \<langle>S\<rangle>list_rel"
    and "(si, s) \<in> R"
    and CR: "(ci, c) \<in> R \<rightarrow> bool_rel"
    and FR: "\<And>xi x si s. \<lbrakk> (xi,x)\<in>S; (si,s)\<in>R; c s \<rbrakk> \<Longrightarrow> fi xi si \<le> \<Down>\<^sub>E E R (f x s)"
  shows "enfoldli li ci fi si \<le> \<Down>\<^sub>E E R (enfoldli l c f s)"
  unfolding enres_unfolds
  apply (rule nfoldli_refine)
  apply (rule assms(1))
  apply (simp add: assms(2))
  subgoal using CR[param_fo] by (auto split: sum.split simp: sum_rel_conv)
  subgoal 
    apply refine_rcg
    applyS (auto split: sum.splits simp: sum_rel_conv)
    apply (rule FR[unfolded enres_unfolds]) 
    by (auto split: sum.splits simp: sum_rel_conv)
  done

lemma EWHILET_refine[refine]:
  assumes R0: "(x,x')\<in>R"
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>\<^sub>E E R (f' x')"
  shows "EWHILET b f x \<le>\<Down>\<^sub>E E R (EWHILET b' f' x')"
  unfolding enres_unfolds
  apply refine_rcg
  using assms
  by (auto split: sum.splits simp: econc_fun_def)

thm WHILEIT_refine

lemma EWHILEIT_refine[refine]:
  assumes R0: "I' x' \<Longrightarrow> (x,x')\<in>R"
  assumes I_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I' x' \<rbrakk> \<Longrightarrow> I x"  
  assumes COND_REF: "\<And>x x'. \<lbrakk> (x,x')\<in>R; I x; I' x' \<rbrakk> \<Longrightarrow> b x = b' x'"
  assumes STEP_REF: 
    "\<And>x x'. \<lbrakk> (x,x')\<in>R; b x; b' x'; I x; I' x' \<rbrakk> \<Longrightarrow> f x \<le> \<Down>\<^sub>E E R (f' x')"
  shows "EWHILEIT I b f x \<le>\<Down>\<^sub>E E R (EWHILEIT I' b' f' x')"
  unfolding enres_unfolds
  apply refine_rcg
  using assms
  by (auto split: sum.splits simp: econc_fun_def)



subsubsection \<open>Refine2- heuristics\<close>

lemma remove_eLet_refine:
  assumes "M \<le> \<Down>\<^sub>E E R (f x)"
  shows "M \<le> \<Down>\<^sub>E E R (Let x f)" using assms by auto

lemma intro_eLet_refine:
  assumes "f x \<le> \<Down>\<^sub>E E R M'"
  shows "Let x f \<le> \<Down>\<^sub>E E R M'" using assms by auto

lemma ebind2let_refine[refine2]:
  assumes "ERETURN x \<le> \<Down>\<^sub>E E R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> f x \<le> \<Down>\<^sub>E E R (f' x')"
  shows "Let x f \<le> \<Down>\<^sub>E E R (ebind M' (\<lambda>x'. f' x'))"
  using assms 
  apply (simp add: pw_ele_iff refine_pw_simps) 
  apply fast
  done

lemma ebind_Let_refine2[refine2]: "\<lbrakk> 
    m' \<le>\<Down>\<^sub>E E R' (ERETURN x);
    \<And>x'. \<lbrakk>inres m' (Inr x'); (x',x)\<in>R'\<rbrakk> \<Longrightarrow> f' x' \<le> \<Down>\<^sub>E E R (f x) 
  \<rbrakk> \<Longrightarrow> ebind m' (\<lambda>x'. f' x') \<le> \<Down>\<^sub>E E R (Let x (\<lambda>x. f x))"
  apply (simp add: pw_ele_iff refine_pw_simps)
  apply blast
  done

lemma ebind2letRETURN_refine[refine2]:
  assumes "ERETURN x \<le> \<Down>\<^sub>E E R' M'"
  assumes "\<And>x'. (x,x')\<in>R' \<Longrightarrow> ERETURN (f x) \<le> \<Down>\<^sub>E E R (f' x')"
  shows "ERETURN (Let x f) \<le> \<Down>\<^sub>E E R (ebind M' (\<lambda>x'. f' x'))"
  using assms
  apply (simp add: pw_ele_iff refine_pw_simps)
  apply fast
  done

lemma ERETURN_as_SPEC_refine[refine2]:
  assumes "RELATES R"
  assumes "M \<le> ESPEC (\<lambda>_. False) (\<lambda>c. (c,a)\<in>R)"
  shows "M \<le> \<Down>\<^sub>E E R (ERETURN a)"
  using assms
  by (simp add: pw_ele_iff refine_pw_simps)

lemma if_ERETURN_refine[refine2]:
  assumes "b \<longleftrightarrow> b'"
  assumes "\<lbrakk>b;b'\<rbrakk> \<Longrightarrow> ERETURN S1 \<le> \<Down>\<^sub>E E R S1'"
  assumes "\<lbrakk>\<not>b;\<not>b'\<rbrakk> \<Longrightarrow> ERETURN S2 \<le> \<Down>\<^sub>E E R S2'"
  shows "ERETURN (if b then S1 else S2) \<le> \<Down>\<^sub>E E R (if b' then S1' else S2')"
  (* this is nice to have for small functions, hence keep it in refine2 *)
  using assms
  by (simp add: pw_le_iff refine_pw_simps)



text \<open>Breaking down enres-monad \<close>
definition enres_lift :: "'a nres \<Rightarrow> (_,'a) enres" where 
  "enres_lift m \<equiv> do { x \<leftarrow> m; RETURN (Inr x) }"

lemma enres_lift_rule[refine_vcg]: "m\<le>SPEC \<Phi> \<Longrightarrow> enres_lift m \<le> ESPEC E \<Phi>"
  by (auto simp: pw_ele_iff pw_le_iff refine_pw_simps enres_lift_def)
  
named_theorems_rev enres_breakdown  
lemma [enres_breakdown]:
  "ERETURN x = enres_lift (RETURN x)"  
  "EASSERT \<Phi> = enres_lift (ASSERT \<Phi>)"
  "doE { x \<leftarrow> enres_lift m; ef x } = do { x \<leftarrow> m; ef x }"
  (*"NO_MATCH (enres_lift m) em \<Longrightarrow> doE { x \<leftarrow> em; ef x } = do { ex \<leftarrow> em; case ex of Inl e \<Rightarrow> RETURN (Inl e) | Inr x \<Rightarrow> ef x }"*)
  unfolding enres_unfolds enres_lift_def
  apply (auto split: sum.splits simp: pw_eq_iff refine_pw_simps)
  done
  
lemma [enres_breakdown]: 
  "do { x \<leftarrow> m; enres_lift (f x) } = enres_lift (do { x \<leftarrow> m; f x })"
  "do { let x = v; enres_lift (f x) } = enres_lift (do { let x=v; f x })"
  unfolding enres_unfolds enres_lift_def
  apply (auto split: sum.splits simp: pw_eq_iff refine_pw_simps)
  done

lemma [enres_breakdown]:
  "CATCH (enres_lift m) h = enres_lift m"  
  unfolding enres_unfolds enres_lift_def
  apply (auto split: sum.splits simp: pw_eq_iff refine_pw_simps)
  done
  
lemma enres_lift_fail[simp]:  "enres_lift FAIL = FAIL"
  unfolding enres_lift_def by auto


(* TODO: Also do breakdown-thm for RECT. It's exactly the same approach! *)
lemma [enres_breakdown]: "EWHILEIT I c (\<lambda>s. enres_lift (f s)) s = enres_lift (WHILEIT I c f s)"
  (is "?lhs = ?rhs")
proof (rule antisym)
  show "?lhs \<le> ?rhs"
    unfolding enres_unfolds WHILEIT_def WHILET_def
    apply (rule RECT_transfer_rel'[where P="\<lambda>c a. c = Inr a"])
    apply (simp add: while.WHILEI_body_trimono)
    apply (simp add: while.WHILEI_body_trimono)
    apply simp
    apply simp
    by (auto simp: WHILEI_body_def enres_lift_def pw_le_iff refine_pw_simps)

  show "?rhs \<le> ?lhs"
    unfolding enres_unfolds WHILEIT_def WHILET_def
    apply (rule RECT_transfer_rel'[where P="\<lambda>a c. c = Inr a"])
    apply (simp add: while.WHILEI_body_trimono)
    apply (simp add: while.WHILEI_body_trimono)
    apply simp
    apply simp
    by (auto simp: WHILEI_body_def enres_lift_def pw_le_iff refine_pw_simps)
qed    



lemma [enres_breakdown]: "EWHILET c (\<lambda>s. enres_lift (f s)) s = enres_lift (WHILET c f s)"
  unfolding EWHILET_def WHILET_def enres_breakdown ..
  
lemma [enres_breakdown]: "enfoldli l c (\<lambda>x s. enres_lift (f x s)) s = enres_lift (nfoldli l c f s)"
  apply (induction l arbitrary: s)
  by (auto simp: enres_breakdown)  
    
    
lemma [enres_breakdown]: 
  "(\<lambda>(a,b). enres_lift (f a b)) = (\<lambda>x. enres_lift (case x of (a,b) \<Rightarrow> f a b))" by auto
  
lemmas [enres_breakdown] = nres_monad_laws nres_bind_let_law

lemma [enres_breakdown]:
  "doE { CHECK \<Phi> e; m } = (if \<Phi> then m else THROW e)"
  by (auto simp: enres_unfolds)

lemma [enres_breakdown]: "(if b then enres_lift m else enres_lift n) = enres_lift (if b then m else n)"
  by simp

lemma option_case_enbd[enres_breakdown]:
  "case_option (enres_lift fn) (\<lambda>v. enres_lift (fs v)) = (\<lambda>x. enres_lift (case_option fn fs x))"
  by (auto split: option.split)
    
    
    
named_theorems enres_inline
    
method opt_enres_unfold = ((unfold enres_inline)?; (unfold enres_monad_laws)?; (unfold enres_breakdown)?; (rule refl)?; (unfold enres_unfolds enres_lift_def nres_monad_laws)?; (rule refl)?)

  
subsection \<open>More Combinators\<close>  
  subsubsection \<open>CHECK-Monadic\<close>
    
  definition [enres_unfolds]: "CHECK_monadic c e \<equiv> doE { b \<leftarrow> c; CHECK b e }"
  
  lemma CHECK_monadic_rule_iff:
    "(CHECK_monadic c e \<le> ESPEC E P) \<longleftrightarrow> (c \<le> ESPEC E (\<lambda>r. (r \<longrightarrow> P ()) \<and> (\<not>r \<longrightarrow> E e)))"
    by (auto simp: pw_ele_iff CHECK_monadic_def refine_pw_simps)
  
  lemma CHECK_monadic_pw[refine_pw_simps]:
    "nofail (CHECK_monadic c e) \<longleftrightarrow> nofail c"
    "inres (CHECK_monadic c e) (Inl ee) \<longleftrightarrow> (inres c (Inl ee) \<or> inres c (Inr False) \<and> ee=e)"
    "inres (CHECK_monadic c e) (Inr x) \<longleftrightarrow> (inres c (Inr True))"
    unfolding CHECK_monadic_def
    by (auto simp: refine_pw_simps)
  
  lemma CHECK_monadic_rule[refine_vcg]:
    assumes "c \<le> ESPEC E (\<lambda>r. (r \<longrightarrow> P ()) \<and> (\<not>r \<longrightarrow> E e))"
    shows "CHECK_monadic c e \<le> ESPEC E P"
    using assms by (simp add: CHECK_monadic_rule_iff)  
  
  lemma CHECK_monadic_refine[refine]:
    assumes "ci \<le> \<Down>\<^sub>E ER bool_rel c"
    assumes "(ei,e)\<in>ER"  
    shows "CHECK_monadic ci ei \<le>\<Down>\<^sub>E ER unit_rel (CHECK_monadic c e)"  
    using assms  
    by (auto simp: pw_ele_iff refine_pw_simps)
  
  lemma CHECK_monadic_CHECK_refine[refine]:
    assumes "ci \<le> ESPEC (\<lambda>e'. (e',e)\<in>ER \<and> \<not>c) (\<lambda>r. r \<longleftrightarrow> c)"
    assumes "(ei,e)\<in>ER"
    shows "CHECK_monadic ci ei \<le>\<Down>\<^sub>E ER unit_rel (CHECK c e)"
    using assms  
    by (auto simp: pw_ele_iff refine_pw_simps)
  
  lemma CHECK_monadic_endb[enres_breakdown]: "CHECK_monadic (enres_lift c) e = 
    do {b \<leftarrow> c; CHECK b e}"
    by (auto simp: enres_unfolds enres_lift_def)
  
  
  
  
  

end
