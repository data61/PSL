theory CFG
imports Main
begin

typedecl symbol

type_synonym rule = "symbol \<times> symbol list"

type_synonym sentence = "symbol list"

locale CFG =
  fixes \<NN> :: "symbol set"
  fixes \<TT> :: "symbol set"
  fixes \<RR> :: "rule set"
  fixes \<SS> :: "symbol"
  assumes disjunct_symbols: "\<NN> \<inter> \<TT> = {}"
  assumes startsymbol_dom: "\<SS> \<in> \<NN>"
  assumes validRules: "\<forall> (N, \<alpha>) \<in> \<RR>. N \<in> \<NN> \<and> (\<forall> s \<in> set \<alpha>. s \<in> \<NN> \<union> \<TT>)"
begin

definition is_terminal :: "symbol \<Rightarrow> bool"
where
  "is_terminal s = (s \<in> \<TT>)"

definition is_nonterminal :: "symbol \<Rightarrow> bool"
where
  "is_nonterminal s = (s \<in> \<NN>)"

lemma is_nonterminal_startsymbol:"is_nonterminal \<SS>"
  by (simp add: is_nonterminal_def startsymbol_dom)

definition is_symbol :: "symbol \<Rightarrow> bool"
where
  "is_symbol s = (is_terminal s \<or> is_nonterminal s)"

definition is_sentence :: "sentence \<Rightarrow> bool"
where
  "is_sentence s = list_all is_symbol s"

definition is_word :: "sentence \<Rightarrow> bool"
where
  "is_word s = list_all is_terminal s"
   
definition derives1 :: "sentence \<Rightarrow> sentence \<Rightarrow> bool"
where
  "derives1 u v = 
     (\<exists> x y N \<alpha>. 
          u = x @ [N] @ y
        \<and> v = x @ \<alpha> @ y
        \<and> is_sentence x
        \<and> is_sentence y
        \<and> (N, \<alpha>) \<in> \<RR>)"  

definition derivations1 :: "(sentence \<times> sentence) set"
where
  "derivations1 = { (u,v) | u v. derives1 u v }"

definition derivations :: "(sentence \<times> sentence) set"
where 
  "derivations = derivations1^*"

definition derives :: "sentence \<Rightarrow> sentence \<Rightarrow> bool"
where
  "derives u v = ((u, v) \<in> derivations)"

definition is_derivation :: "sentence \<Rightarrow> bool"
where
  "is_derivation u = derives [\<SS>] u"

definition \<L> :: "sentence set"
where
  "\<L> = { v | v. is_word v \<and> is_derivation v}"

definition "\<L>\<^sub>P"  :: "sentence set"
where
  "\<L>\<^sub>P = { u | u v. is_word u \<and> is_derivation (u@v) }"

end

end

