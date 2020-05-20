(*  Title:       Conflict analysis/List Interleaving Operator
    Author:      Peter Lammich <peter.lammich@uni-muenster.de>
    Maintainer:  Peter Lammich <peter.lammich@uni-muenster.de>
*)
section "List Interleaving Operator"
theory Interleave
imports Main "HOL-Library.Permutation" Misc
begin
text_raw \<open>\label{thy:Interleave}\<close>

text \<open>
  This theory defines an operator to return the set of all possible interleavings of two lists.
\<close>

(*
  Is \<Otimes>-operator needed ?
    Should we better do a reformulation of \<otimes> on sets of lists, to get an associative, commutative operator with identity (ACI ?) ?
*)

subsection "Definitions"

subsubsection "Prepend and concatenate lifted to sets"

definition list_set_cons :: "'a \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr "\<cdot>" 65)
  where [simp]: "a\<cdot>S = (#) a ` S"

definition list_set_append :: "'a list \<Rightarrow> 'a list set \<Rightarrow> 'a list set" (infixr "\<odot>" 65)
  where [simp]: "a\<odot>S = (@) a ` S"

subsubsection "The interleaving operator"

function
  interleave :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list set" (infixr "\<otimes>" 64)
where
  "[]\<otimes>b = {b}"
  | "a\<otimes>[] = {a}"
  | "a#l \<otimes> b#r = ((a\<cdot>(l \<otimes> b#r)) \<union> (b\<cdot>(a#l \<otimes> r)))"
by pat_completeness auto
termination by lexicographic_order


subsection "Properties"

subsubsection "Lifted prepend and concatenate operators"
lemma cons_set_cons_eq: "a#l \<in> b\<cdot>S = (a=b & l\<in>S)"
  by auto
lemma append_set_append_eq: "\<lbrakk>length a = length b\<rbrakk> \<Longrightarrow> a@l \<in> b\<odot>S = (a=b & l\<in>S)"
  by auto

lemma list_set_cons_cases[cases set]: "\<lbrakk>w\<in>a\<cdot>S; !!w'. \<lbrakk> w=a#w'; w'\<in>S \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto
lemma list_set_append_cases[cases set]: "\<lbrakk>w\<in>a\<odot>S; !!w'. \<lbrakk> w=a@w'; w'\<in>S \<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by auto

subsubsection "Standard simplification-, introduction-, elimination-, and induction rules"
lemma interleave_cons1: "l \<in> a\<otimes>b \<Longrightarrow> x#l \<in> x#a \<otimes> b"
  apply(case_tac b)
  apply(auto)
done
  
lemma interleave_cons2: "l \<in> a\<otimes>b \<Longrightarrow> x#l \<in> a \<otimes> x#b"
  apply(case_tac a)
  apply(auto)
done

lemmas interleave_cons = interleave_cons1 interleave_cons2


lemma interleave_empty[simp]: "[]\<in>a\<otimes>b = (a=[] & b=[])"
  apply(case_tac a)
  apply(case_tac b)
  apply(simp)
  apply(simp)
  apply(case_tac b)
  apply(auto)
done

(* TODO: Is this wise as default simp ?*)
lemma interleave_length[rule_format, simp]: "ALL x : a\<otimes>b . length x = length a + length b"
  apply(induct rule: interleave.induct)
  apply(auto)
done

lemma interleave_same[simp]: "y\<in>l\<otimes>y = (l=[])"
  apply (rule iffI)
  apply (subgoal_tac "length y = length l + length y")
  apply (simp del: interleave_length)
  apply (erule interleave_length)
  apply simp
done

lemma interleave_comm[simp]: "a\<otimes>b = b\<otimes>a" (is "?P f a b")
  apply(induct rule: interleave.induct)
  apply(auto)
done

lemma interleave_cont_conc[rule_format, simp]: "ALL b . a@b \<in> a\<otimes>b"
  apply(induct_tac a)
  apply(auto simp add: interleave_cons)
done

lemma interleave_cont_rev_conc[simp]: "b@a \<in> a\<otimes>b"
  apply (subgoal_tac "b@a \<in> b\<otimes>a")
  apply(simp)
  apply(simp only: interleave_cont_conc)
done

lemma interleave_not_empty: "a\<otimes>b ~= {}" 
  apply(induct rule: interleave.induct)
  apply(auto)
done

lemma cons_interleave_split: "\<lbrakk>a#l \<in> l1\<otimes>l2\<rbrakk> \<Longrightarrow> (EX lh . l1=a#lh & l \<in> lh\<otimes>l2 | l2=a#lh & l \<in> l1\<otimes>lh )"
  apply(case_tac l1)
  apply(auto)
  apply(case_tac l2)
  apply(auto)
done

lemma cons_interleave_cases[cases set, case_names left right]: "\<lbrakk>a#l \<in> l1\<otimes>l2; !!lh . \<lbrakk>l1=a#lh; l \<in> lh\<otimes>l2\<rbrakk> \<Longrightarrow> P; !!lh. \<lbrakk>l2=a#lh; l \<in> l1\<otimes>lh\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
  by (blast dest: cons_interleave_split)

lemma interleave_cases[cases set, case_names empty left right]: "\<lbrakk>l\<in>l1\<otimes>l2; \<lbrakk> l=[]; l1=[]; l2=[] \<rbrakk> \<Longrightarrow> P; !!a l' l1'. \<lbrakk>l=a#l'; l1=a#l1'; l'\<in>l1'\<otimes>l2\<rbrakk> \<Longrightarrow> P; !!a l' l2'. \<lbrakk>l=a#l'; l2=a#l2'; l'\<in>l1\<otimes>l2'\<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  apply (cases l)
  apply (simp)
  apply simp
  apply (erule cons_interleave_cases)
  apply simp_all
  done

lemma interleave_elem_induct[induct set, case_names empty left right]: 
  "!!w1 w2. \<lbrakk> w\<in>w1\<otimes>w2; P [] [] []; !!e w w1 w2. \<lbrakk> P w w1 w2; w\<in>w1\<otimes>w2 \<rbrakk> \<Longrightarrow> P (e#w) (e#w1) w2; !!e w w1 w2. \<lbrakk> P w w1 w2; w\<in>w1\<otimes>w2 \<rbrakk> \<Longrightarrow> P (e#w) w1 (e#w2) \<rbrakk> \<Longrightarrow> P w w1 w2"
  by (induct w) (auto elim!: cons_interleave_cases intro!: interleave_cons)

lemma interleave_rev_cons1[rule_format]: "ALL a b . l \<in> a\<otimes>b \<longrightarrow> l@[x] \<in> a@[x] \<otimes> b" (is "?P l") 
proof (induct l)
  case Nil show ?case by (simp)
  case (Cons e l)
    assume IH[rule_format]: "?P l"
    show "?P (e#l)" proof (intro allI impI)
      fix a b
      assume "e#l \<in> a\<otimes>b"
      then obtain c where SPLIT: "a=e#c & l\<in>c\<otimes>b | b=e#c & l\<in>a\<otimes>c" by (blast dest: cons_interleave_split)
      with IH have "a=e#c & l@[x]\<in>c@[x]\<otimes>b | b=e#c & l@[x]\<in>a@[x]\<otimes>c" by auto
      hence "a=e#c & e#l@[x]\<in>e#c@[x]\<otimes>b | b=e#c & e#l@[x]\<in>a@[x]\<otimes>e#c" by (auto simp add: interleave_cons)
      thus "(e#l)@[x]\<in>a@[x]\<otimes>b" by auto
    qed
qed

corollary interleave_rev_cons2: "l \<in> a\<otimes>b \<Longrightarrow> l@[x] \<in> a \<otimes> b@[x]"
proof -
  assume "l \<in> a\<otimes>b"
  hence "l\<in>b\<otimes>a" by auto
  hence "l@[x] \<in> b@[x] \<otimes> a" by (blast dest: interleave_rev_cons1)
  thus ?thesis by auto
qed

lemmas interleave_rev_cons = interleave_rev_cons1 interleave_rev_cons2


subsubsection "Interleaving and list concatenation"

lemma interleave_append1: "\<lbrakk>l \<in> a\<otimes>b\<rbrakk> \<Longrightarrow> x@l \<in> x@a \<otimes> b" proof -
  have "ALL l a b . l \<in> a\<otimes>b \<longrightarrow> x@l \<in> x@a \<otimes> b" (is "?P x") proof (induct x)
    show "?P []" by simp
  next
    fix e
    fix x::"'a list"
    assume IH: "?P x"
    show "?P (e#x)" proof (intro impI allI)
      fix l::"'a list" 
      fix a b
      assume "l \<in> a \<otimes> b"
      with IH have "x@l \<in> x@a \<otimes> b" by auto
      with interleave_cons1 show "(e # x) @ l \<in> (e # x) @ a \<otimes> b" by force
    qed
  qed
  moreover assume "l \<in> a \<otimes> b"
  ultimately show ?thesis by blast
qed

lemma interleave_append2: "\<lbrakk>l \<in> a\<otimes>b\<rbrakk> \<Longrightarrow> x@l \<in> a \<otimes> x@b" proof -
  have "ALL l a b . l \<in> a\<otimes>b \<longrightarrow> x@l \<in> a \<otimes> x@b" (is "?P x") proof (induct x)
    show "?P []" by simp
  next
    fix a 
    fix x::"'a list"
    assume IH: "\<forall>l a b. l \<in> a \<otimes> b \<longrightarrow> x @ l \<in> a \<otimes> x @ b"
    show "\<forall>l aa b. l \<in> aa \<otimes> b \<longrightarrow> (a # x) @ l \<in> aa \<otimes> (a # x) @ b" proof (intro impI allI)
      fix l::"'a list" 
      fix aa b
      assume "l \<in> aa \<otimes> b"

      with IH have "x@l \<in> aa \<otimes> x@b" by auto
      with interleave_cons2 show "(a # x) @ l \<in> aa \<otimes> (a # x) @ b" by force
    qed
  qed
  moreover assume "l \<in> a \<otimes> b"
  ultimately show ?thesis by blast
qed

lemmas interleave_append = interleave_append1 interleave_append2

lemma interleave_rev_append1: "!!a b w. w\<in>a\<otimes>b \<Longrightarrow> w@w' \<in> a@w' \<otimes> b"
proof (induct w' rule: rev_induct)
  case Nil thus ?case by simp
next
  case (snoc e w') note IHP=this
  hence "w@w'\<in>a@w'\<otimes>b" by auto
  thus ?case using interleave_rev_cons1[of "w@w'" "a@w'" "b"] by (simp)
qed
lemma interleave_rev_append2: "w\<in>a\<otimes>b \<Longrightarrow> w@w' \<in> a \<otimes> b@w'"
  by (simp only: interleave_comm[of a b] interleave_comm[of a "b@w'"]) (blast dest: interleave_rev_append1)
lemmas interleave_rev_append = interleave_rev_append1 interleave_rev_append2

lemma interleave_rev1[rule_format]: "ALL w1 w2 . (w\<in>w1\<otimes>w2) \<longrightarrow> (rev w \<in> rev w1 \<otimes> rev w2)" (is "?P w")
proof (induct w)
  case Nil show ?case by (simp)
  case (Cons e w)
    assume IH[rule_format]: "?P w"
    show ?case proof (clarsimp)
      fix w1 w2
      assume "e # w \<in> w1 \<otimes> w2"
      then obtain w' where "w1=e#w' & w\<in>w'\<otimes>w2 | w2=e#w' & w\<in>w1\<otimes>w'" by (blast dest: cons_interleave_split)
      with IH have "w1=e#w' & rev w\<in>rev w' \<otimes> rev w2 | w2=e#w' & rev w \<in> rev w1 \<otimes> rev w'" by auto
      thus "rev w @ [e]\<in>rev w1 \<otimes> rev w2" by (auto simp add: interleave_rev_cons)
    qed
qed

corollary interleave_rev2: "(rev w \<in> rev w1 \<otimes> rev w2) \<Longrightarrow> (w\<in>w1\<otimes>w2)" 
  apply (subgoal_tac "(rev w\<in>rev w1\<otimes>rev w2) = (rev (rev w) \<in> rev (rev w1) \<otimes> rev (rev w2))")
  apply(simp)
  apply (blast dest: interleave_rev1)
done

lemmas interleave_rev = interleave_rev1 interleave_rev2

lemma rev_cons_interleave_split: "\<lbrakk>l@[a] \<in> l1\<otimes>l2\<rbrakk> \<Longrightarrow> (EX lh . l1=lh@[a] & l \<in> lh\<otimes>l2 | l2=lh@[a] & l \<in> l1\<otimes>lh )"
proof -
  assume "l@[a] \<in> l1\<otimes>l2"
  hence "a#rev l \<in> rev l1 \<otimes> rev l2" by (auto dest: interleave_rev)
  then obtain lh where "rev l1 = a#lh & rev l \<in> lh\<otimes>rev l2 | rev l2 = a#lh & rev l \<in> rev l1 \<otimes> lh" by (blast dest: cons_interleave_split)
  hence "rev l1 = a#lh & l \<in> rev lh \<otimes> l2 | rev l2 = a#lh & l \<in> l1 \<otimes> rev lh" by (auto dest: interleave_rev)
  hence "l1 = rev lh @ [a] & l \<in> rev lh \<otimes> l2 | l2 = rev lh @ [a] & l \<in> l1 \<otimes> rev lh" by (simp add: rev_swap)
  thus ?thesis by blast
qed

subsubsection "Associativity"
 
lemma interleave_s_assoc1[rule_format]: "ALL w1 ws w2 w3 . (w\<in>w1\<otimes>ws & ws\<in>w2\<otimes>w3 \<longrightarrow> (EX ws' : w1\<otimes>w2 . w \<in> ws'\<otimes>w3))" proof (induct w)
  case Nil show ?case by (auto)
  case (Cons e w)
    assume IH: "ALL w1 ws w2 w3 . w\<in>w1\<otimes>ws & ws\<in>w2\<otimes>w3 \<longrightarrow> (EX ws' : w1\<otimes>w2 . w \<in> ws'\<otimes>w3)"
    show ?case proof (intro impI allI)
      fix w1 ws w2 w3
      assume A: "e#w \<in> w1 \<otimes> ws \<and> ws \<in> w2 \<otimes> w3"
      then obtain wh where CASES: "w1=e#wh & w\<in>wh\<otimes>ws | ws=e#wh & w\<in>w1\<otimes>wh" by (blast dest!: cons_interleave_split)
      moreover {
        assume CASE: "w1=e#wh & w\<in>wh\<otimes>ws"
        with A IH obtain ws' where "ws'\<in>wh\<otimes>w2 & w\<in>ws'\<otimes>w3" by (blast)
        hence "e#ws'\<in> (e#wh)\<otimes>w2 & e#w \<in> (e#ws')\<otimes>w3" by (auto simp add: interleave_cons)
        with CASE have "\<exists>ws'\<in>w1 \<otimes> w2. e # w \<in> ws' \<otimes> w3" by blast
      } moreover {
        assume CASE: "ws=e#wh & w\<in>w1\<otimes>wh"
        with A obtain whh where "w2=e#whh & wh\<in>whh\<otimes>w3 | w3=e#whh & wh\<in>w2\<otimes>whh" by (blast dest!: cons_interleave_split)
        moreover {
          assume SCASE: "w2=e#whh & wh\<in>whh\<otimes>w3"
          with CASE IH obtain ws' where "ws'\<in>w1\<otimes>whh & w\<in>ws'\<otimes>w3" by blast
          with SCASE have "e#ws'\<in>w1\<otimes>w2 & e#w \<in> (e#ws')\<otimes>w3" by (auto simp add: interleave_cons)
          hence "\<exists>ws'\<in>w1 \<otimes> w2. e # w \<in> ws' \<otimes> w3" by blast
        } moreover {
          assume SCASE: "w3=e#whh & wh\<in>w2\<otimes>whh"
          with CASE IH obtain ws' where "ws'\<in>w1\<otimes>w2 & w\<in>ws'\<otimes>whh" by blast
          with SCASE have "ws'\<in>w1\<otimes>w2 & e#w \<in> ws'\<otimes>w3" by (auto simp add: interleave_cons)
          hence "\<exists>ws'\<in>w1 \<otimes> w2. e # w \<in> ws' \<otimes> w3" by blast
        } ultimately have "\<exists>ws'\<in>w1 \<otimes> w2. e # w \<in> ws' \<otimes> w3" by blast
      } ultimately show "\<exists>ws'\<in>w1 \<otimes> w2. e # w \<in> ws' \<otimes> w3" by blast
    qed
qed

lemma interleave_s_assoc2: "\<lbrakk>w\<in>ws\<otimes>w3; ws\<in>w1\<otimes>w2\<rbrakk> \<Longrightarrow> EX ws' : w2\<otimes>w3 . w \<in> w1\<otimes>ws'" proof -
  assume "w \<in> ws \<otimes> w3" "ws \<in> w1 \<otimes> w2"
  hence "w \<in> w3 \<otimes> ws & ws \<in> w2 \<otimes> w1" by simp
  hence "EX ws':w3\<otimes>w2 . w\<in>ws'\<otimes>w1" by (simp only: interleave_s_assoc1)
  thus ?thesis by simp
qed
  
lemmas interleave_s_assoc = interleave_s_assoc1 interleave_s_assoc2

subsubsection "Relation to other standard list operations"

lemma interleave_set: "w\<in>w1\<otimes>w2 \<Longrightarrow> set w = set w1 \<union> set w2"
  by (induct rule: interleave_elem_induct) auto
lemma interleave_map: "w\<in>w1\<otimes>w2 \<Longrightarrow> map f w \<in> map f w1 \<otimes> map f w2"
  by (induct rule: interleave_elem_induct) (auto intro!: interleave_cons)
lemma interleave_filter: "w\<in>w1\<otimes>w2 \<Longrightarrow> filter f w \<in> filter f w1 \<otimes> filter f w2"
  by (induct rule: interleave_elem_induct) (auto intro!: interleave_cons)


subsubsection "Relation to sublist order"

lemma ileq_interleave_alt: "l'\<preceq>l == \<exists>lb. l\<in>lb \<otimes> l'" proof (rule eq_reflection)
  {fix l' l have "l'\<preceq>l \<Longrightarrow> \<exists>lb. l\<in>lb \<otimes> l'" by (induct rule: less_eq_list_induct) (simp, (blast intro: interleave_cons)+)}
  moreover {fix l have "!!lb l'. l\<in>lb\<otimes>l' \<Longrightarrow> l'\<preceq>l" by (induct l) (auto intro: less_eq_list_drop elim!: cons_interleave_cases)}
  ultimately show "(l'\<preceq>l) = (\<exists>lb. l\<in>lb \<otimes> l')" by blast
qed

lemma ileq_interleave: "w\<in>w1\<otimes>w2 \<Longrightarrow> w1\<preceq>w & w2\<preceq>w"
  by (unfold ileq_interleave_alt, auto)

lemma ilt_ex_notempty: "x < y \<longleftrightarrow> (\<exists>xs. xs \<noteq> [] \<and> y \<in> xs \<otimes> x)"
  apply (auto simp add: order_less_le ileq_interleave_alt)
  apply (case_tac lb)
  apply auto
done


lemma ilt_interleave1: "\<lbrakk>w\<in>w1\<otimes>w2; w1~=[]\<rbrakk> \<Longrightarrow> w2<w"
  by (simp only: ilt_ex_notempty, blast)
lemma ilt_interleave2: "\<lbrakk>w\<in>w1\<otimes>w2; w2~=[]\<rbrakk> \<Longrightarrow> w1<w"
  by (simp only: ilt_ex_notempty interleave_comm[of w1 w2], blast)
lemmas ilt_interleave = ilt_interleave1 ilt_interleave2


subsubsection "Exotic/specialized lemmas"
\<comment> \<open>Recover structure of @{text w} wrt. to structure of @{text "w1"}\<close>
lemma interleave_recover1[rule_format]: "ALL w1a w1b w2 . w\<in>(w1a@w1b)\<otimes>w2 \<longrightarrow> (EX wa wb w2a w2b . w=wa@wb & w2=w2a@w2b & wa\<in>w1a\<otimes>w2a & wb\<in>w1b\<otimes>w2b)" 
  (is "?P w" is "ALL w1a w1b w2 . ?PRE w w1a w1b w2 \<longrightarrow> ?CONS w w1a w1b w2")
proof (induct w)
  case Nil show ?case by (auto)
  case (Cons e w)
    assume IH[rule_format]: "?P w"
    show "?P (e#w)" proof (intro allI impI)
      fix w1a w1b w2
      assume PRE: "e # w \<in> w1a @ w1b \<otimes> w2"
      {
        assume CASE: "w1a=[]"
        with PRE have "e#w=[]@(e#w) & w2=[]@w2 & []\<in>w1a\<otimes>[] & e#w\<in>w1b\<otimes>w2" by (auto)
        hence "?CONS (e#w) w1a w1b w2" by blast
      } moreover {
        assume CASE: "w1a~=[]"
        with PRE obtain wh where SCASES: "w1a@w1b=e#wh & w\<in>wh\<otimes>w2 | w2=e#wh & w\<in>w1a@w1b\<otimes>wh" by (blast dest: cons_interleave_split)
        moreover {
          assume SCASE: "w1a@w1b=e#wh & w\<in>wh\<otimes>w2"
          with CASE obtain w1ah where W1AFMT: "w1a=e#w1ah & w1ah@w1b=wh" by (cases w1a, auto)
          with SCASE have "w\<in>w1ah@w1b\<otimes>w2" by auto
          with IH[of w1ah w1b w2] obtain wa wb w2a w2b where "w=wa@wb & w2=w2a@w2b & wa\<in>w1ah\<otimes>w2a & wb\<in>w1b\<otimes>w2b" by (blast)
          with W1AFMT have "e#w=(e#wa)@wb & e#w\<in>e#wa\<otimes>wb & w2=w2a@w2b & e#wa\<in>w1a\<otimes>w2a & wb\<in>w1b\<otimes>w2b" by (auto simp add: interleave_cons)
          hence "?CONS (e#w) w1a w1b w2" by blast
        } moreover {
          assume SCASE: "w2=e#wh & w\<in>w1a@w1b\<otimes>wh"
          with IH[of w1a w1b wh] obtain wa wb w2a w2b where "w=wa@wb & wh=w2a@w2b & wa\<in>w1a\<otimes>w2a & wb\<in>w1b\<otimes>w2b" by blast
          with SCASE have "e#w=(e#wa)@wb & w2=(e#w2a)@w2b & e#wa\<in>w1a\<otimes>e#w2a & wb\<in>w1b\<otimes>w2b" by (auto simp add: interleave_cons)
          hence "?CONS (e#w) w1a w1b w2" by blast
        }
        ultimately have "?CONS (e#w) w1a w1b w2" by blast
      }
      ultimately show "?CONS (e#w) w1a w1b w2" by blast
    qed
qed

lemma interleave_recover2: "w\<in>w1\<otimes>(w2a@w2b) \<Longrightarrow> EX wa wb w1a w1b . w=wa@wb & w1=w1a@w1b & wa\<in>w1a\<otimes>w2a & wb\<in>w1b\<otimes>w2b"
proof -
  assume "w\<in>w1\<otimes>(w2a@w2b)"
  hence "w\<in>(w2a@w2b)\<otimes>w1" by auto
  hence "EX wa wb w1a w1b . w=wa@wb & w1=w1a@w1b & wa\<in>w2a\<otimes>w1a & wb\<in>w2b\<otimes>w1b" by (blast dest: interleave_recover1)
  thus ?thesis by auto
qed

lemmas interleave_recover = interleave_recover1 interleave_recover2

\<comment> \<open>Split operands according to element of result\<close>
lemma interleave_unconc: "!! l2 w1 w2 . l1@l2 \<in> w1\<otimes>w2 \<Longrightarrow> \<exists> w11 w12 w21 w22 . w1=w11@w12 \<and> w2=w21@w22 \<and> l1\<in>w11\<otimes>w21 \<and> l2\<in>w12\<otimes>w22"
proof (induct l1)
  case Nil hence "w1=[]@w1 & w2=[]@w2 & []\<in>[]\<otimes>[] & l2\<in>w1\<otimes>w2" by auto
  thus ?case by fast
next
  case (Cons e l1') note IHP=this
  hence "e#(l1'@l2)\<in>w1\<otimes>w2" by auto
  with cons_interleave_split obtain w' where "(w1=e#w' & l1'@l2\<in>w'\<otimes>w2) | (w2=e#w' & l1'@l2\<in>w1\<otimes>w')" (is "?C1 | ?C2") by (fast)
  moreover {
    assume CASE: ?C1
    moreover then obtain w11' w12' w21 w22 where "w'=w11'@w12' \<and> w2=w21@w22 \<and> l1'\<in>w11'\<otimes>w21 \<and> l2\<in>w12'\<otimes>w22" by (fast dest: IHP(1))
    moreover hence "e#w'=(e#w11')@w12' & e#l1'\<in>(e#w11')\<otimes>w21" by (auto dest: interleave_cons)
    ultimately have ?case by fast
  } moreover {
    assume CASE: ?C2
    moreover then obtain w11 w12 w21' w22' where "w1=w11@w12 \<and> w'=w21'@w22' \<and> l1'\<in>w11\<otimes>w21' \<and> l2\<in>w12\<otimes>w22'" by (fast dest: IHP(1))
    moreover hence "e#w'=(e#w21')@w22' & e#l1'\<in>w11\<otimes>(e#w21')" by (auto dest: interleave_cons)
    ultimately have ?case by fast
  } ultimately show ?case by fast
qed

\<comment> \<open>Reverse direction of @{thm [source] "interleave_unconc"}\<close>
lemma interleave_reconc: "!!w11 w21 l2 w12 w22 . \<lbrakk>l1\<in>w11\<otimes>w21;l2\<in>w12\<otimes>w22\<rbrakk> \<Longrightarrow> l1@l2\<in>(w11@w12)\<otimes>(w21@w22)"
proof (induct l1)
  case Nil thus ?case by (auto)
next
  case (Cons e l1') note IHP=this
  then obtain w' where "(w11=e#w' & l1'\<in>w'\<otimes>w21) | (w21=e#w' & l1'\<in>w11\<otimes>w')" (is "?C1 | ?C2") by (fast dest: cons_interleave_split)
  moreover {
    assume CASE: ?C1
    moreover with IHP have "l1'@l2\<in>(w'@w12)\<otimes>(w21@w22)" by auto
    ultimately have ?case by (auto dest: interleave_cons)
  } moreover {
    assume CASE: ?C2
    moreover with IHP have "l1'@l2\<in>(w11@w12)\<otimes>(w'@w22)" by auto
    ultimately have ?case by (auto dest: interleave_cons)
  } ultimately show ?case by fast
qed

(* interleave_unconc and interleave_reconc as equivalence *)
lemma interleave_unconc_eq: "!! l2 w1 w2 . l1@l2 \<in> w1\<otimes>w2 = (\<exists> w11 w12 w21 w22 . w1=w11@w12 \<and> w2=w21@w22 \<and> l1\<in>w11\<otimes>w21 \<and> l2\<in>w12\<otimes>w22)"
  by (fast dest: interleave_reconc interleave_unconc)


end
