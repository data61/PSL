(*  Title:       Conflict analysis/Labelled transition systems
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section \<open>Labeled transition systems\<close>
theory LTS
imports Main
begin
text_raw \<open>\label{thy:LTS}\<close>

text \<open>
  Labeled transition systems (LTS) provide a model of a state transition system with named transitions.
\<close>

subsection \<open>Definitions\<close>
text \<open>An LTS is modeled as a ternary relation between start configuration, transition label and end configuration\<close>
type_synonym ('c,'a) LTS = "('c \<times> 'a \<times> 'c) set"

text \<open>Transitive reflexive closure\<close>

inductive_set 
  trcl :: "('c,'a) LTS \<Rightarrow> ('c,'a list) LTS"
  for t
  where
  empty[simp]: "(c,[],c) \<in> trcl t"
  | cons[simp]: "\<lbrakk> (c,a,c') \<in> t; (c',w,c'') \<in> trcl t \<rbrakk> \<Longrightarrow> (c,a#w,c'') \<in> trcl t"

subsection \<open>Basic properties of transitive reflexive closure\<close>
lemma trcl_empty_cons: "(c,[],c')\<in>trcl t \<Longrightarrow> (c=c')"
  by (auto elim: trcl.cases)
lemma trcl_empty_simp[simp]: "(c,[],c')\<in>trcl t = (c=c')"
  by (auto elim: trcl.cases intro: trcl.intros)

lemma trcl_single[simp]: "((c,[a],c') \<in> trcl t) = ((c,a,c') \<in> t)"
  by (auto elim: trcl.cases)
lemma trcl_uncons: "(c,a#w,c')\<in>trcl t \<Longrightarrow> \<exists>ch . (c,a,ch)\<in>t \<and> (ch,w,c') \<in> trcl t"
  by (auto elim: trcl.cases)
lemma trcl_uncons_cases: "\<lbrakk>
    (c,e#w,c')\<in>trcl S; 
    !!ch. \<lbrakk> (c,e,ch)\<in>S; (ch,w,c')\<in>trcl S \<rbrakk> \<Longrightarrow> P 
  \<rbrakk> \<Longrightarrow> P"
  by (blast dest: trcl_uncons)
lemma trcl_one_elem: "(c,e,c')\<in>t \<Longrightarrow> (c,[e],c')\<in>trcl t"
  by auto

lemma trcl_unconsE[cases set, case_names split]: "\<lbrakk> 
    (c,e#w,c')\<in>trcl S; 
    !!ch. \<lbrakk>(c,e,ch)\<in>S; (ch,w,c')\<in>trcl S\<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (blast dest: trcl_uncons)
lemma trcl_pair_unconsE[cases set, case_names split]: "\<lbrakk> 
    ((s,c),e#w,(s',c'))\<in>trcl S; 
    !!sh ch. \<lbrakk>((s,c),e,(sh,ch))\<in>S; ((sh,ch),w,(s',c'))\<in>trcl S\<rbrakk> \<Longrightarrow> P
  \<rbrakk> \<Longrightarrow> P"
  by (fast dest: trcl_uncons)

lemma trcl_concat: "!! c . \<lbrakk> (c,w1,c')\<in>trcl t; (c',w2,c'')\<in>trcl t \<rbrakk> 
  \<Longrightarrow> (c,w1@w2,c'')\<in>trcl t" 
proof (induct w1)
  case Nil thus ?case by (subgoal_tac "c=c'") auto
next
  case (Cons a w) thus ?case by (auto dest: trcl_uncons) 
qed    
  
lemma trcl_unconcat: "!! c . (c,w1@w2,c')\<in>trcl t 
  \<Longrightarrow> \<exists>ch . (c,w1,ch)\<in>trcl t \<and> (ch,w2,c')\<in>trcl t" 
proof (induct w1)
  case Nil hence "(c,[],c)\<in>trcl t \<and> (c,w2,c')\<in>trcl t" by auto
  thus ?case by fast
next
  case (Cons a w1) note IHP = this
  hence "(c,a#(w1@w2),c')\<in>trcl t" by simp (* Auto/fast/blast do not get the point _#(_@_) = (_#_)@_ in next step, so making it explicit *)
  with trcl_uncons obtain chh where "(c,a,chh)\<in>t \<and> (chh,w1@w2,c')\<in>trcl t" by fast
  moreover with IHP obtain ch where "(chh,w1,ch)\<in>trcl t \<and> (ch,w2,c')\<in>trcl t" by fast
  ultimately have "(c,a#w1,ch)\<in>trcl t \<and> (ch,w2,c')\<in>trcl t" by auto
  thus ?case by fast
qed

subsubsection "Appending of elements to paths"
lemma trcl_rev_cons: "\<lbrakk> (c,w,ch)\<in>trcl T; (ch,e,c')\<in>T \<rbrakk> \<Longrightarrow> (c,w@[e],c')\<in>trcl T"
  by (auto dest: trcl_concat iff add: trcl_single)
lemma trcl_rev_uncons: "(c,w@[e],c')\<in>trcl T 
  \<Longrightarrow> \<exists>ch. (c,w,ch)\<in>trcl T \<and> (ch,e,c')\<in>T"
  by (force dest: trcl_unconcat)
lemma trcl_rev_induct[induct set, consumes 1, case_names empty snoc]: "!! c'. \<lbrakk> 
    (c,w,c')\<in>trcl S; 
    !!c. P c [] c; 
    !!c w c' e c''. \<lbrakk> (c,w,c')\<in>trcl S; (c',e,c'')\<in>S; P c w c' \<rbrakk> \<Longrightarrow> P c (w@[e]) c'' 
  \<rbrakk> \<Longrightarrow> P c w c'"
  by (induct w rule: rev_induct) (auto dest: trcl_rev_uncons)
lemma trcl_rev_cases: "!!c c'. \<lbrakk> 
    (c,w,c')\<in>trcl S; 
    \<lbrakk>w=[]; c=c'\<rbrakk>\<Longrightarrow>P; 
    !!ch e wh. \<lbrakk> w=wh@[e]; (c,wh,ch)\<in>trcl S; (ch,e,c')\<in>S \<rbrakk>\<Longrightarrow>P 
  \<rbrakk> \<Longrightarrow> P"
  by (induct w rule: rev_induct) (auto dest: trcl_rev_uncons)

lemma trcl_cons2: "\<lbrakk> (c,e,ch)\<in>T; (ch,f,c')\<in>T \<rbrakk> \<Longrightarrow> (c,[e,f],c')\<in>trcl T"
  by auto

subsubsection "Transitivity reasoning setup"
declare trcl_cons2[trans]    \<comment> \<open>It's important that this is declared before @{thm [source] trcl_concat}, because we want @{thm [source] trcl_concat} to be tried first by the transitivity reasoner\<close>
declare cons[trans]
declare trcl_concat[trans]
declare trcl_rev_cons[trans]

subsubsection "Monotonicity"
lemma trcl_mono: "!!A B. A \<subseteq> B \<Longrightarrow> trcl A \<subseteq> trcl B" (* FIXME: Why can't this be declared as [mono] or [mono_set] ? *) 
  apply (clarsimp)
  apply (erule trcl.induct)
  apply auto
done

lemma trcl_inter_mono: "x\<in>trcl (S\<inter>R) \<Longrightarrow> x\<in>trcl S" "x\<in>trcl (S\<inter>R) \<Longrightarrow> x\<in>trcl R"
proof -
  assume "x\<in>trcl (S\<inter>R)"
  with trcl_mono[of "S\<inter>R" S] show "x\<in>trcl S" by auto
next
  assume "x\<in>trcl (S\<inter>R)"
  with trcl_mono[of "S\<inter>R" R] show "x\<in>trcl R" by auto
qed


subsubsection "Special lemmas for reasoning about states that are pairs"
lemmas trcl_pair_induct = trcl.induct[of "(xc1,xc2)" "xb" "(xa1,xa2)", split_format (complete), consumes 1, case_names empty cons]
lemmas trcl_rev_pair_induct = trcl_rev_induct[of "(xc1,xc2)" "xb" "(xa1,xa2)", split_format (complete), consumes 1, case_names empty snoc]

(*lemma trcl_pair_induct[induct set]: 
  "\<lbrakk>((xc1,xc2), xb, (xa1,xa2)) \<in> trcl t; \<And>c1 c2. P c1 c2 [] c1 c2; \<And>a c1 c2 c1' c2' c1'' c2'' w. \<lbrakk>((c1,c2), a, (c1',c2')) \<in> t; ((c1',c2'), w, (c1'',c2'')) \<in> trcl t; P c1' c2' w c1'' c2''\<rbrakk> \<Longrightarrow> P c1 c2 (a # w) c1'' c2''\<rbrakk> 
  \<Longrightarrow> P xc1 xc2 xb xa1 xa2" 
  using trcl.induct[of "(xc1,xc2)" xb "(xa1,xa2)" t "\<lambda>c w c'. let (c1,c2)=c in let (c1',c2')=c' in P c1 c2 w c1' c2'"] by auto
*)

subsubsection "Invariants"
(* TODO: Do we really need this ? Is this formulation usable ? *)
lemma trcl_prop_trans[cases set, consumes 1, case_names empty steps]: "\<lbrakk>
    (c,w,c')\<in>trcl S; 
    \<lbrakk>c=c'; w=[]\<rbrakk> \<Longrightarrow> P;  
    \<lbrakk>c\<in>Domain S; c'\<in>Range (Range S)\<rbrakk>\<Longrightarrow>P 
  \<rbrakk> \<Longrightarrow> P"
  apply (erule_tac trcl_rev_cases)
  apply auto
  apply (erule trcl.cases)
  apply auto
  done


end
