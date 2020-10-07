(*  Title:      statecharts/DataSpace/Contrib.thy
    Author:     Steffen Helke and Florian Kammüller, Software Engineering Group
    Copyright   2010 Technische Universitaet Berlin
*)

section \<open>Contributions to the Standard Library of HOL\<close>

theory Contrib
imports Main
begin

subsection \<open>Basic definitions and lemmas\<close>

subsubsection \<open>Lambda expressions\<close>                  

definition restrict :: "['a => 'b, 'a set] => ('a => 'b)" where
 "restrict f A = (%x. if x : A then f x else (@ y. True))"

syntax (ASCII)
  "_lambda_in" :: "[pttrn, 'a set, 'a => 'b] => ('a => 'b)"  ("(3%_:_./ _)" [0, 0, 3] 3)
syntax
  "_lambda_in" :: "[pttrn, 'a set, 'a => 'b] => ('a => 'b)"  ("(3\<lambda>_\<in>_./ _)" [0, 0, 3] 3)
translations 
  "\<lambda>x\<in>A. f"  == "CONST restrict (%x. f) A"


subsubsection \<open>Maps\<close>                  

definition chg_map :: "('b => 'b) => 'a => ('a \<rightharpoonup> 'b) => ('a \<rightharpoonup> 'b)" where  
 "chg_map f a m = (case m a of None => m | Some b => m(a|->f b))"

lemma map_some_list [simp]:
   "map the (map Some L) = L"
apply (induct_tac L)
apply auto
done

lemma dom_ran_the:
  "\<lbrakk> ran G = {y}; x \<in> (dom G) \<rbrakk> \<Longrightarrow> (the (G x)) = y"
apply (unfold ran_def dom_def)
apply auto
done

lemma dom_None:
  "(S \<notin> dom F) \<Longrightarrow> (F S = None)"
by (unfold dom_def, auto)

lemma ran_dom_the:
  "\<lbrakk> y \<notin> Union (ran G); x \<in> dom G \<rbrakk> \<Longrightarrow> y \<notin> the (G x)"
by (unfold ran_def dom_def, auto)

lemma dom_map_upd: "dom(m(a|->b)) = insert a (dom m)"
apply auto
done

subsubsection \<open>\<open>rtrancl\<close>\<close>

lemma rtrancl_Int:
 "\<lbrakk> (a,b) \<in> A; (a,b) \<in> B \<rbrakk> \<Longrightarrow> (a,b) \<in> (A \<inter>  B)^*"
by auto

lemma rtrancl_mem_Sigma:
 "\<lbrakk> a \<noteq> b; (a, b) \<in> (A \<times> A)^* \<rbrakk> \<Longrightarrow> b \<in> A"
apply (frule rtranclD)
apply (cut_tac r="A \<times> A" and A=A in trancl_subset_Sigma)
apply auto
done

lemma help_rtrancl_Range:
 "\<lbrakk> a \<noteq> b; (a,b) \<in> R ^* \<rbrakk> \<Longrightarrow> b \<in> Range R"
apply (erule rtranclE)
apply auto
done

lemma rtrancl_Int_help:
  "(a,b) \<in> (A \<inter> B) ^*  ==> (a,b) \<in> A^* \<and> (a,b) \<in> B^*"
apply (unfold Int_def)
apply auto
apply (rule_tac b=b in rtrancl_induct)
apply auto
apply (rule_tac b=b in rtrancl_induct)
apply auto
done

lemmas rtrancl_Int1 = rtrancl_Int_help [THEN conjunct1]
lemmas rtrancl_Int2 = rtrancl_Int_help [THEN conjunct2]

lemma tranclD3 [rule_format]:
  "(S,T) \<in> R^+ \<Longrightarrow> (S,T) \<notin> R \<longrightarrow> (\<exists> U. (S,U) \<in> R \<and> (U,T) \<in> R^+)"
apply (rule_tac a="S" and b="T" and r=R in trancl_induct)
apply auto
done

lemma tranclD4 [rule_format]:
  "(S,T) \<in> R^+ \<Longrightarrow> (S,T) \<notin> R \<longrightarrow> (\<exists> U. (S,U) \<in> R^+ \<and> (U,T) \<in> R)"
apply (rule_tac a="S" and b="T" and r=R in trancl_induct)
apply auto
done

lemma trancl_collect [rule_format]:
  "\<lbrakk> (x,y) \<in> R^*; S \<notin> Domain R \<rbrakk> \<Longrightarrow> y \<noteq> S \<longrightarrow> (x,y) \<in> {p. fst p \<noteq> S \<and> snd p \<noteq> S \<and> p \<in> R}^*"
apply (rule_tac b=y in rtrancl_induct)
apply auto
apply (rule rtrancl_into_rtrancl)
apply fast
apply auto
done

lemma trancl_subseteq:
  "\<lbrakk> R \<subseteq> Q; S \<in> R^* \<rbrakk> \<Longrightarrow> S \<in> Q^*"
apply (frule rtrancl_mono)
apply fast
done

lemma trancl_Int_subset:
   "(R \<inter> (A \<times> A))\<^sup>+ \<subseteq> R\<^sup>+ \<inter> (A \<times> A)"
apply (rule subsetI) 
apply (rename_tac S)
apply (case_tac "S")
apply (rename_tac T V)
apply auto
apply (rule_tac a=T and b=V and r="(R  \<inter> A \<times> A)" in converse_trancl_induct, auto)+
done

lemma trancl_Int_mem:
   "(S,T) \<in> (R \<inter> (A \<times> A))\<^sup>+ \<Longrightarrow> (S,T)  \<in> R\<^sup>+ \<inter> A \<times> A"
by (rule trancl_Int_subset [THEN subsetD], assumption)

lemma Int_expand: 
  "{(S,S'). P S S' \<and>  Q S S'} = ({(S,S'). P S S'} \<inter> {(S,S'). Q S S'})"
by auto

subsubsection \<open>\<open>finite\<close>\<close>

lemma finite_conj:  
 "finite ({(S,S'). P S S'}::(('a*'b)set)) \<longrightarrow>  
     finite {(S,S'). P (S::'a) (S'::'b) \<and> Q (S::'a) (S'::'b)}"
apply (rule impI)
apply (subst Int_expand)
apply (rule finite_Int)
apply auto
done

lemma finite_conj2:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> finite ({(S,S'). S: A \<and> S' : B})"
by auto

subsubsection \<open>\<open>override\<close>\<close>

lemma dom_override_the:
  "(x \<in> (dom G2)) \<longrightarrow> ((G1 ++ G2) x) = (G2 x)"
by (auto)

lemma dom_override_the2 [simp]:
  "\<lbrakk> dom G1 \<inter> dom G2 = {}; x \<in> (dom G1) \<rbrakk> \<Longrightarrow> ((G1 ++ G2) x) = (G1 x)"
apply (unfold dom_def map_add_def)
apply auto
apply (drule sym)
apply (erule equalityE)
apply (unfold Int_def)
apply auto
apply (erule_tac x=x in allE)
apply auto
done 

lemma dom_override_the3 [simp]:
  "\<lbrakk> x \<notin> dom G2; x \<in> dom G1 \<rbrakk> \<Longrightarrow> ((G1 ++ G2) x) = (G1 x)"
apply (unfold dom_def map_add_def)
apply auto
done

lemma Union_ran_override [simp]:
  "S \<in> dom G \<Longrightarrow> \<Union> (ran (G ++ Map.empty(S \<mapsto> insert SA (the(G S))))) = 
   (insert SA (Union (ran G)))"
apply (unfold dom_def ran_def)
apply auto
apply (rename_tac T)
apply (case_tac "T = S")
apply auto
done

lemma Union_ran_override2 [simp]:
  "S \<in> dom G \<Longrightarrow> \<Union> (ran (G(S \<mapsto> insert SA (the(G S))))) = (insert SA (Union (ran G)))"
apply (unfold dom_def ran_def)
apply auto
apply (rename_tac T)
apply (case_tac "T = S")
apply auto
done

lemma ran_override [simp]:
  "(dom A \<inter> dom B) = {} \<Longrightarrow> ran (A ++ B) = (ran A) \<union> (ran B)"
apply (unfold Int_def ran_def)
apply (simp add: map_add_Some_iff)
apply auto
done

lemma chg_map_new [simp]:
  "m a = None \<Longrightarrow> chg_map f a m = m"
by (unfold chg_map_def, auto)

lemma chg_map_upd [simp]:
  "m a = Some b \<Longrightarrow> chg_map f a m = m(a|->f b)"
by (unfold chg_map_def, auto)

lemma ran_override_chg_map:
  "A \<in> dom G \<Longrightarrow> ran (G ++ Map.empty(A|->B)) = (ran (chg_map (\<lambda> x. B) A G))"
apply (unfold dom_def ran_def)
apply (subst map_add_Some_iff [THEN ext])
apply auto
apply (rename_tac T)
apply (case_tac "T = A")
apply auto
done

subsubsection \<open>\<open>Part\<close>\<close>

definition  Part :: "['a set, 'b => 'a] => 'a set" where
            "Part A h = A \<inter> {x. \<exists> z. x = h(z)}"
 

lemma Part_UNIV_Inl_comp: 
 "((Part UNIV (Inl o f)) = (Part UNIV (Inl o g))) = ((Part UNIV f) = (Part UNIV g))"
apply (unfold Part_def)
apply auto
apply (erule equalityE)
apply (erule subsetCE)
apply auto
apply (erule equalityE)
apply (erule subsetCE)
apply auto
done

lemma Part_eqI [intro]: "\<lbrakk> a \<in> A; a=h(b) \<rbrakk> \<Longrightarrow> a \<in> Part A h"
by (auto simp add: Part_def)

lemmas PartI = Part_eqI [OF _ refl]

lemma PartE [elim!]: "\<lbrakk> a \<in> Part A h;  !!z. \<lbrakk> a \<in> A;  a=h(z) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (auto simp add: Part_def)

lemma Part_subset: "Part A h \<subseteq> A"
by (auto simp add: Part_def)

lemma Part_mono: "A \<subseteq> B \<Longrightarrow> Part A h \<subseteq> Part B h"
by blast

lemmas basic_monos = basic_monos Part_mono

lemma PartD1: "a \<in> Part A h \<Longrightarrow> a \<in> A"
by (simp add: Part_def)

lemma Part_id: "Part A (\<lambda> x. x) = A"
by blast

lemma Part_Int: "Part (A \<inter> B) h = (Part A h) \<inter> (Part B h)"
by blast

lemma Part_Collect: "Part (A \<inter> {x. P x}) h = (Part A h) \<inter> {x. P x}"
by blast

subsubsection \<open>Set operators\<close>

lemma subset_lemma:
  "\<lbrakk> A \<inter> B = {}; A \<subseteq> B \<rbrakk> \<Longrightarrow> A = {}"
by auto

lemma subset_lemma2:
 "\<lbrakk> B \<inter> A = {}; C \<subseteq> A \<rbrakk> \<Longrightarrow> C \<inter> B = {}"
by auto

lemma insert_inter:
  "\<lbrakk> a \<notin> A; (A \<inter> B) = {} \<rbrakk> \<Longrightarrow> (A \<inter> (insert a B)) = {}"
by auto

lemma insert_notmem:
  "\<lbrakk> a \<noteq> b; a \<notin> B \<rbrakk> \<Longrightarrow> a \<notin> (insert b B)"
by auto

lemma insert_union:
 "A \<union> (insert a B) = insert a A \<union> B"
by auto

lemma insert_or:
     "{s. s = t1 \<or>  (P s)} = insert t1 {s. P s }"
by auto

lemma Collect_subset: 
  "{x . x \<subseteq> A \<and> P x} = {x \<in> Pow A. P x}"
by auto

lemma OneElement_Card [simp]:
  "\<lbrakk> finite M; card M <= Suc 0; t \<in> M \<rbrakk> \<Longrightarrow> M = {t}"
apply auto
apply (rename_tac s)
apply (rule_tac P="finite M" in mp)
apply (rule_tac P="card M <= Suc 0" in mp)
apply (rule_tac P="t \<in> M" in mp)
apply (rule_tac F="M" in finite_induct)
apply auto
apply (rule_tac P="finite M" in mp)
apply (rule_tac P="card M <= Suc 0" in mp)
apply (rule_tac P="s \<in> M" in mp)
apply (rule_tac P="t \<in> M" in mp)
apply (rule_tac F="M" in finite_induct)
apply auto
done 
  
subsubsection \<open>One point rule\<close>

lemma Ex1_one_point [simp]: 
  "(\<exists>! x. P x \<and> x = a) = P a"
by auto

lemma Ex1_one_point2 [simp]:
  "(\<exists>! x. P x \<and> Q x \<and> x = a) = (P a \<and> Q a)"
by auto

lemma Some_one_point [simp]:
 "P a \<Longrightarrow> (SOME x. P x \<and> x = a) = a"
by auto

lemma Some_one_point2 [simp]:
 "\<lbrakk> Q a; P a \<rbrakk> \<Longrightarrow> (SOME x. P x \<and> Q x \<and> x = a) = a"
by auto

end
