section "2-3 Finger Trees" 

theory FingerTree
imports Main
begin

text \<open>
  We implement and prove correct 2-3 finger trees as described by Ralf Hinze 
  and Ross Paterson\cite{HiPa06}.
\<close>

text \<open>
  This theory is organized as follows: 
  Section~\ref{sec:datatype} contains the finger-tree datatype, its invariant
  and its abstraction function to lists.
  The Section~\ref{sec:operations} contains the operations 
  on finger trees and their correctness lemmas.
  Section~\ref{sec:hide_invar} contains a finger tree datatype with implicit
  invariant, and, finally, Section~\ref{sec:doc} contains a documentation
  of the implemented operations.
\<close>

text_raw \<open>\paragraph{Technical Issues}\<close>
text \<open>
  As Isabelle lacks proper support of namespaces, we
  try to simulate namespaces by locales.

  The problem is, that we define lots of internal functions that
  should not be exposed to the user at all.
  Moreover, we define some functions with names equal to names
  from Isabelle's standard library. These names make perfect sense
  in the context of FingerTrees, however, they shall not be exposed 
  to anyone using this theory indirectly, hiding the standard library
  names there.

  Our approach puts all functions and lemmas inside the locale 
  {\em FingerTree\_loc},
  and then interprets this locale with the prefix {\em FingerTree}.
  This makes all definitions visible outside the locale, with
  qualified names. Inside the locale, however, one can use unqualified names.
\<close>

subsection "Datatype definition"
text_raw\<open>\label{sec:datatype}\<close>
locale FingerTreeStruc_loc

text \<open>
  Nodes: Non empty 2-3 trees, with all elements stored within the leafs plus a 
  cached annotation 
\<close>
datatype ('e,'a) Node = Tip 'e 'a |
  Node2 'a "('e,'a) Node" "('e,'a) Node" | 
  Node3 'a "('e,'a) Node" "('e,'a) Node" "('e,'a) Node"

  text \<open>Digit: one to four ordered Nodes\<close>
datatype ('e,'a) Digit = One "('e,'a) Node" |
   Two "('e,'a) Node" "('e,'a) Node" |
   Three "('e,'a) Node" "('e,'a) Node" "('e,'a) Node" |
   Four "('e,'a) Node" "('e,'a) Node" "('e,'a) Node" "('e,'a) Node"

  text \<open>FingerTreeStruc: 
    The empty tree, a single node or some nodes and a deeper tree\<close>
datatype ('e, 'a) FingerTreeStruc = 
  Empty |
  Single "('e,'a) Node" |
  Deep 'a "('e,'a) Digit" "('e,'a) FingerTreeStruc" "('e,'a) Digit"

subsubsection "Invariant"

context FingerTreeStruc_loc
begin
text_raw \<open>\paragraph{Auxiliary functions}\ \\\<close>

  text \<open>Readout the cached annotation of a node\<close>
primrec gmn :: "('e,'a::monoid_add) Node \<Rightarrow> 'a" where
  "gmn (Tip e a) = a" |
  "gmn (Node2 a _ _) = a" |
  "gmn (Node3 a _ _ _) = a"

  text \<open>The annotation of a digit is computed on the fly\<close>
primrec gmd :: "('e,'a::monoid_add) Digit \<Rightarrow> 'a" where
  "gmd (One a) = gmn a" |
  "gmd (Two a b) = (gmn a) + (gmn b)"|
  "gmd (Three a b c) = (gmn a) + (gmn b) + (gmn c)"|
  "gmd (Four a b c d) = (gmn a) + (gmn b) + (gmn c) + (gmn d)"

  text \<open>Readout the cached annotation of a finger tree\<close>
primrec gmft :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> 'a" where
  "gmft Empty = 0" |
  "gmft (Single nd) = gmn nd" |
  "gmft (Deep a _ _ _) = a"

text \<open>Depth and cached annotations have to be correct\<close>

fun is_leveln_node :: "nat \<Rightarrow> ('e,'a) Node \<Rightarrow> bool" where
  "is_leveln_node 0 (Tip _ _) \<longleftrightarrow> True" |
  "is_leveln_node (Suc n) (Node2 _ n1 n2) \<longleftrightarrow> 
    is_leveln_node n n1 \<and> is_leveln_node n n2" |
  "is_leveln_node (Suc n) (Node3 _ n1 n2 n3) \<longleftrightarrow> 
    is_leveln_node n n1 \<and> is_leveln_node n n2 \<and> is_leveln_node n n3" |
  "is_leveln_node _ _ \<longleftrightarrow> False"

primrec is_leveln_digit :: "nat \<Rightarrow> ('e,'a) Digit \<Rightarrow> bool" where
  "is_leveln_digit n (One n1) \<longleftrightarrow> is_leveln_node n n1" |
  "is_leveln_digit n (Two n1 n2) \<longleftrightarrow> is_leveln_node n n1 \<and> 
    is_leveln_node n n2" |
  "is_leveln_digit n (Three n1 n2 n3) \<longleftrightarrow> is_leveln_node n n1 \<and> 
    is_leveln_node n n2 \<and> is_leveln_node n n3" |
  "is_leveln_digit n (Four n1 n2 n3 n4) \<longleftrightarrow> is_leveln_node n n1 \<and> 
    is_leveln_node n n2 \<and> is_leveln_node n n3 \<and> is_leveln_node n n4"

primrec is_leveln_ftree :: "nat \<Rightarrow> ('e,'a) FingerTreeStruc \<Rightarrow> bool" where
  "is_leveln_ftree n Empty \<longleftrightarrow> True" |
  "is_leveln_ftree n (Single nd) \<longleftrightarrow> is_leveln_node n nd" |
  "is_leveln_ftree n (Deep _ l t r) \<longleftrightarrow> is_leveln_digit n l \<and> 
    is_leveln_digit n r \<and> is_leveln_ftree (Suc n) t"

primrec is_measured_node :: "('e,'a::monoid_add) Node \<Rightarrow> bool" where
  "is_measured_node (Tip _ _) \<longleftrightarrow> True" |
  "is_measured_node (Node2 a n1 n2) \<longleftrightarrow> ((is_measured_node n1) \<and> 
    (is_measured_node n2)) \<and> (a = (gmn n1) + (gmn n2))" |
  "is_measured_node (Node3 a n1 n2 n3) \<longleftrightarrow> ((is_measured_node n1) \<and> 
    (is_measured_node n2) \<and> (is_measured_node n3)) \<and> 
    (a = (gmn n1) + (gmn n2) + (gmn n3))"

primrec is_measured_digit :: "('e,'a::monoid_add) Digit \<Rightarrow> bool" where
  "is_measured_digit (One a) = is_measured_node a" |
  "is_measured_digit (Two a b) = 
    ((is_measured_node a) \<and> (is_measured_node b))"|
  "is_measured_digit (Three a b c) = 
    ((is_measured_node a) \<and> (is_measured_node b) \<and> (is_measured_node c))"|
  "is_measured_digit (Four a b c d) = ((is_measured_node a) \<and> 
    (is_measured_node b) \<and> (is_measured_node c) \<and> (is_measured_node d))"

primrec is_measured_ftree :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> bool" where
  "is_measured_ftree Empty \<longleftrightarrow> True" |
  "is_measured_ftree (Single n1) \<longleftrightarrow> (is_measured_node n1)" |
  "is_measured_ftree (Deep a l m r) \<longleftrightarrow> ((is_measured_digit l) \<and> 
    (is_measured_ftree m) \<and> (is_measured_digit r)) \<and> 
    (a = ((gmd l) + (gmft m) + (gmd r)))"

text "Structural invariant for finger trees"
definition "ft_invar t == is_leveln_ftree 0 t \<and> is_measured_ftree t"

subsubsection "Abstraction to Lists"

primrec nodeToList :: "('e,'a) Node \<Rightarrow> ('e \<times> 'a) list" where
  "nodeToList (Tip e a) = [(e,a)]"|
  "nodeToList (Node2 _ a b) = (nodeToList a) @ (nodeToList b)"|
  "nodeToList (Node3 _ a b c) 
    = (nodeToList a) @ (nodeToList b) @ (nodeToList c)"

primrec digitToList :: "('e,'a) Digit \<Rightarrow> ('e \<times> 'a) list" where
  "digitToList (One a) = nodeToList a"|
  "digitToList (Two a b) = (nodeToList a) @ (nodeToList b)"|
  "digitToList (Three a b c) 
    = (nodeToList a) @ (nodeToList b) @ (nodeToList c)"|
  "digitToList (Four a b c d) 
    = (nodeToList a) @ (nodeToList b) @ (nodeToList c) @ (nodeToList d)"

text "List representation of a finger tree"
primrec toList :: "('e ,'a) FingerTreeStruc \<Rightarrow> ('e \<times> 'a) list" where
  "toList Empty = []"|
  "toList (Single a) = nodeToList a"|
  "toList (Deep _ pr m sf) = (digitToList pr) @ (toList m) @ (digitToList sf)"

lemma nodeToList_empty: "nodeToList nd \<noteq> Nil"
  by (induct nd) auto

lemma digitToList_empty: "digitToList d \<noteq> Nil"
  by (cases d, auto simp add: nodeToList_empty)

text \<open>Auxiliary lemmas\<close>
lemma gmn_correct:
  assumes "is_measured_node nd"
  shows "gmn nd = sum_list (map snd (nodeToList nd))"
  by (insert assms, induct nd) (auto simp add: add.assoc)

lemma gmd_correct:
  assumes "is_measured_digit d"
  shows "gmd d = sum_list (map snd (digitToList d))"
  by (insert assms, cases d, auto simp add: gmn_correct add.assoc)

lemma gmft_correct: "is_measured_ftree t 
  \<Longrightarrow> (gmft t) = sum_list (map snd (toList t))"
  by (induct t, auto simp add: ft_invar_def gmd_correct gmn_correct add.assoc)
lemma gmft_correct2: "ft_invar t \<Longrightarrow> (gmft t) = sum_list (map snd (toList t))"
  by (simp only: ft_invar_def gmft_correct)

subsection \<open>Operations\<close>
text_raw\<open>\label{sec:operations}\<close>

subsubsection \<open>Empty tree\<close>
lemma Empty_correct[simp]: 
  "toList Empty = []"
  "ft_invar Empty"
  by (simp_all add: ft_invar_def)

text \<open>Exactly the empty finger tree represents the empty list\<close>
lemma toList_empty: "toList t = [] \<longleftrightarrow> t = Empty"
  by (induct t, auto simp add: nodeToList_empty digitToList_empty)

subsubsection \<open>Annotation\<close>
text "Sum of annotations of all elements of a finger tree"
definition annot :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> 'a"
  where "annot t = gmft t"

lemma annot_correct:
  "ft_invar t \<Longrightarrow> annot t = sum_list (map snd (toList t))"
  using gmft_correct
  unfolding annot_def
  by (simp add: gmft_correct2)

subsubsection \<open>Appending\<close>

text \<open>Auxiliary functions to fill in the annotations\<close>
definition deep:: "('e,'a::monoid_add) Digit \<Rightarrow> ('e,'a) FingerTreeStruc 
    \<Rightarrow> ('e,'a) Digit \<Rightarrow> ('e, 'a) FingerTreeStruc" where
  "deep pr m sf = Deep ((gmd pr) + (gmft m) + (gmd sf)) pr m sf"
definition node2 where
  "node2 nd1 nd2 = Node2 ((gmn nd1)+(gmn nd2)) nd1 nd2"
definition node3 where
  "node3 nd1 nd2 nd3 = Node3 ((gmn nd1)+(gmn nd2)+(gmn nd3)) nd1 nd2 nd3"

text "Append a node at the left end"
fun nlcons :: "('e,'a::monoid_add) Node \<Rightarrow> ('e,'a) FingerTreeStruc 
    \<Rightarrow> ('e,'a) FingerTreeStruc"  
where
\<comment> \<open>Recursively we append a node, if the digit is full we push down a node3\<close>
  "nlcons a Empty = Single a" |
  "nlcons a (Single b) = deep (One a) Empty (One b)" |
  "nlcons a (Deep _ (One b) m sf) = deep (Two a b) m sf" |
  "nlcons a (Deep _ (Two b c) m sf) = deep (Three a b c) m sf" |
  "nlcons a (Deep _ (Three b c d) m sf) = deep (Four a b c d) m sf" |
  "nlcons a (Deep _ (Four b c d e) m sf) 
    = deep (Two a b) (nlcons (node3 c d e) m) sf"

text "Append a node at the right end"
fun nrcons :: "('e,'a::monoid_add) FingerTreeStruc 
    \<Rightarrow> ('e,'a) Node \<Rightarrow> ('e,'a) FingerTreeStruc"  where
  \<comment> \<open>Recursively we append a node, if the digit is full we push down a node3\<close>
  "nrcons Empty a = Single a" |
  "nrcons (Single b) a = deep (One b) Empty (One a)" |
  "nrcons (Deep _ pr m (One b)) a = deep pr m (Two  b a)"|
  "nrcons (Deep _ pr m (Two b c)) a = deep pr m (Three b c a)" |
  "nrcons (Deep _ pr m (Three b c d)) a = deep pr m (Four b c d a)" |
  "nrcons (Deep _ pr m (Four b c d e)) a 
    = deep pr (nrcons m (node3 b c d)) (Two e a)"

lemma nlcons_invlevel: "\<lbrakk>is_leveln_ftree n t; is_leveln_node n nd\<rbrakk> 
  \<Longrightarrow> is_leveln_ftree n (nlcons nd t)"
  by (induct t arbitrary: n nd rule: nlcons.induct) 
(auto simp add: deep_def node3_def)

lemma nlcons_invmeas: "\<lbrakk>is_measured_ftree t; is_measured_node nd\<rbrakk> 
  \<Longrightarrow> is_measured_ftree (nlcons nd t)"
  by (induct t arbitrary: nd rule: nlcons.induct) 
     (auto simp add: deep_def node3_def)

lemmas nlcons_inv = nlcons_invlevel nlcons_invmeas

lemma nlcons_list: "toList (nlcons a t) = (nodeToList a) @ (toList t)"
  apply (induct t arbitrary: a rule: nlcons.induct)
  apply (auto simp add: deep_def toList_def node3_def)
done

lemma nrcons_invlevel: "\<lbrakk>is_leveln_ftree n t; is_leveln_node n nd\<rbrakk> 
  \<Longrightarrow> is_leveln_ftree n (nrcons t nd)"
  apply (induct t nd arbitrary: nd n rule:nrcons.induct) 
  apply(auto simp add: deep_def node3_def)
  done

lemma nrcons_invmeas: "\<lbrakk>is_measured_ftree t; is_measured_node nd\<rbrakk> 
  \<Longrightarrow> is_measured_ftree (nrcons t nd)"
  apply (induct t nd arbitrary: nd rule:nrcons.induct) 
  apply(auto simp add: deep_def node3_def)
  done

lemmas nrcons_inv = nrcons_invlevel nrcons_invmeas

lemma nrcons_list: "toList (nrcons t a) = (toList t) @ (nodeToList a)"
  apply (induct t a arbitrary: a rule: nrcons.induct)
  apply (auto simp add: deep_def toList_def node3_def)
done

text "Append an element at the left end"
definition lcons :: "('e \<times> 'a::monoid_add) 
    \<Rightarrow> ('e,'a) FingerTreeStruc \<Rightarrow> ('e,'a) FingerTreeStruc" (infixr "\<lhd>" 65) where
  "a \<lhd> t = nlcons (Tip (fst a) (snd a)) t"

lemma lcons_correct: 
  assumes "ft_invar t" 
  shows "ft_invar (a \<lhd> t)" and "toList (a \<lhd> t) = a # (toList t)"
  using assms
  unfolding ft_invar_def
  by (simp_all add: lcons_def nlcons_list nlcons_invlevel nlcons_invmeas)

lemma lcons_inv:"ft_invar t \<Longrightarrow> ft_invar (a \<lhd> t)"
  by (rule lcons_correct)

lemma lcons_list[simp]: "toList (a \<lhd> t) = a # (toList t)"
  by (simp add: lcons_def nlcons_list)

text "Append an element at the right end"
definition rcons 
  :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e \<times> 'a) \<Rightarrow> ('e,'a) FingerTreeStruc"
      (infixl "\<rhd>" 65) where
  "t \<rhd> a = nrcons t (Tip (fst a) (snd a))"

lemma rcons_correct: 
  assumes "ft_invar t" 
  shows "ft_invar (t \<rhd> a)" and "toList (t \<rhd> a) = (toList t) @ [a]"
  using assms
  by (auto simp add: nrcons_inv ft_invar_def rcons_def nrcons_list)

lemma rcons_inv:"ft_invar t \<Longrightarrow> ft_invar (t \<rhd> a)"
  by (rule rcons_correct)

lemma rcons_list[simp]: "toList (t \<rhd> a) = (toList t) @ [a]"
  by(auto simp add: nrcons_list rcons_def) 


subsubsection \<open>Convert list to tree\<close>
primrec toTree :: "('e \<times> 'a::monoid_add) list \<Rightarrow> ('e,'a) FingerTreeStruc" where
  "toTree [] = Empty"|
  "toTree (a#xs) = a \<lhd> (toTree xs)"

lemma toTree_correct[simp]:
  "ft_invar (toTree l)"
  "toList (toTree l) = l"
  apply (induct l)
  apply (simp add: ft_invar_def)
  apply simp
  apply (simp add: toTree_def lcons_list lcons_inv)
  apply (simp add: toTree_def lcons_list lcons_inv)
  done

text \<open>
  Note that this lemma is a completeness statement of our implementation, 
  as it can be read as:
  ,,All lists of elements have a valid representation as a finger tree.''
\<close>

subsubsection \<open>Detaching leftmost/rightmost element\<close>

primrec digitToTree :: "('e,'a::monoid_add) Digit \<Rightarrow> ('e,'a) FingerTreeStruc" 
  where
  "digitToTree (One a) = Single a"|
  "digitToTree (Two a b) = deep (One a) Empty (One b)"|
  "digitToTree (Three a b c) = deep (Two a b) Empty (One c)"|
  "digitToTree (Four a b c d) = deep (Two a b) Empty (Two c d)"

primrec nodeToDigit :: "('e,'a) Node \<Rightarrow> ('e,'a) Digit" where
  "nodeToDigit (Tip e a) = One (Tip e a)"|
  "nodeToDigit (Node2 _ a b) = Two a b"|
  "nodeToDigit (Node3 _ a b c) = Three a b c"

fun nlistToDigit :: "('e,'a) Node list \<Rightarrow> ('e,'a) Digit" where
  "nlistToDigit [a] = One a" |
  "nlistToDigit [a,b] = Two a b" |
  "nlistToDigit [a,b,c] = Three a b c" |
  "nlistToDigit [a,b,c,d] = Four a b c d"

primrec digitToNlist :: "('e,'a) Digit \<Rightarrow> ('e,'a) Node list" where
  "digitToNlist (One a) = [a]" |
  "digitToNlist (Two a b) = [a,b] " |
  "digitToNlist (Three a b c) = [a,b,c]" |
  "digitToNlist (Four a b c d) = [a,b,c,d]"

text \<open>Auxiliary function to unwrap a Node element\<close> 
primrec n_unwrap:: "('e,'a) Node \<Rightarrow> ('e \<times> 'a)" where
  "n_unwrap (Tip e a) = (e,a)"|
  "n_unwrap (Node2 _ a b) = undefined"|
  "n_unwrap (Node3 _ a b c) = undefined"


type_synonym ('e,'a) ViewnRes = "(('e,'a) Node \<times> ('e,'a) FingerTreeStruc) option"
lemma viewnres_cases:
  fixes r :: "('e,'a) ViewnRes"
  obtains (Nil) "r=None" |
          (Cons) a t where "r=Some (a,t)"
  by (cases r) auto

lemma viewnres_split: 
  "P (case_option f1 (case_prod f2) x) = 
  ((x = None \<longrightarrow> P f1) \<and> (\<forall>a b. x = Some (a,b) \<longrightarrow> P (f2 a b)))"
  by (auto split: option.split prod.split)

text \<open>Detach the leftmost node. Return @{const None} on empty finger tree.\<close>
fun viewLn :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) ViewnRes" where
  "viewLn Empty = None"|
  "viewLn (Single a) = Some (a, Empty)"| 
  "viewLn (Deep _ (Two a b) m sf) = Some (a, (deep (One b) m sf))"|
  "viewLn (Deep _ (Three a b c) m sf) = Some (a, (deep (Two b c) m sf))"|
  "viewLn (Deep _ (Four a b c d) m sf) = Some (a, (deep (Three b c d) m sf))"|
  "viewLn (Deep _ (One a) m sf) = 
    (case viewLn m of 
      None \<Rightarrow> Some (a, (digitToTree sf)) |
      Some (b, m2) \<Rightarrow> Some (a, (deep (nodeToDigit b) m2 sf)))"


text \<open>Detach the rightmost node. Return @{const None} on empty finger tree.\<close>
fun viewRn :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) ViewnRes" where
  "viewRn Empty = None" |
  "viewRn (Single a) = Some (a, Empty)" | 
  "viewRn (Deep _ pr m (Two a b)) = Some (b, (deep pr m (One a)))" |
  "viewRn (Deep _ pr m (Three a b c)) = Some (c, (deep pr m (Two a b)))" |
  "viewRn (Deep _ pr m (Four a b c d)) = Some (d, (deep pr m (Three a b c)))" |
  "viewRn (Deep _ pr m (One a)) = 
    (case viewRn m of 
      None \<Rightarrow> Some (a, (digitToTree pr))|
      Some (b, m2) \<Rightarrow> Some (a, (deep pr m2 (nodeToDigit b))))"

(* TODO: Head, last geht auch in O(1) !!! *)

lemma 
  digitToTree_inv: "is_leveln_digit n d \<Longrightarrow> is_leveln_ftree n (digitToTree d)"
  "is_measured_digit d \<Longrightarrow> is_measured_ftree (digitToTree d)" 
  apply (cases d,auto simp add: deep_def)
  apply (cases d,auto simp add: deep_def)
  done

lemma digitToTree_list: "toList (digitToTree d) = digitToList d"
  by (cases d) (auto simp add: deep_def)

lemma nodeToDigit_inv:
  "is_leveln_node (Suc n) nd \<Longrightarrow> is_leveln_digit n (nodeToDigit nd) " 
  "is_measured_node nd \<Longrightarrow> is_measured_digit (nodeToDigit nd)"
  by (cases nd, auto) (cases nd, auto)

lemma nodeToDigit_list: "digitToList (nodeToDigit nd) = nodeToList nd"
  by (cases nd,auto)



lemma viewLn_empty: "t \<noteq> Empty \<longleftrightarrow> (viewLn t) \<noteq> None"
proof (cases t)
  case Empty thus ?thesis by simp
next
  case (Single Node) thus ?thesis by simp
next
  case (Deep a l x r) thus ?thesis 
  apply(auto)
  apply(case_tac l)
  apply(auto)
  apply(cases "viewLn x")
  apply(auto)
  done
qed

lemma viewLn_inv: "\<lbrakk>
  is_measured_ftree t; is_leveln_ftree n t; viewLn t = Some (nd, s)
  \<rbrakk> \<Longrightarrow> is_measured_ftree s \<and> is_measured_node nd \<and> 
        is_leveln_ftree n s \<and> is_leveln_node n nd"
  apply(induct t arbitrary: n nd s rule: viewLn.induct)
  apply(simp add: viewLn_empty)
  apply(simp)
  apply(auto simp add: deep_def)[1]
  apply(auto simp add: deep_def)[1]
  apply(auto simp add: deep_def)[1]
proof -
  fix ux a m sf n nd s
  assume av: "\<And>n nd s.
           \<lbrakk>is_measured_ftree m; is_leveln_ftree n m; viewLn m = Some (nd, s)\<rbrakk>
           \<Longrightarrow> is_measured_ftree s \<and>
              is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd "
         " is_measured_ftree (Deep ux (One a) m sf) "
         "is_leveln_ftree n (Deep ux (One a) m sf)"
         "viewLn (Deep ux (One a) m sf) = Some (nd, s)"
  thus "is_measured_ftree s \<and>
          is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd"
  proof (cases "viewLn m" rule: viewnres_cases)
    case Nil
    with av(4) have v1: "nd = a" "s = digitToTree sf"
    by auto
    from v1 av(2,3) show "is_measured_ftree s \<and>
       is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd"
       apply(auto)
       apply(auto simp add: digitToTree_inv)
    done
  next
    case (Cons b m2)
    with av(4) have v2: "nd = a" "s = (deep (nodeToDigit b) m2 sf)" 
    apply (auto simp add: deep_def)
    done
    note myiv = av(1)[of "Suc n" b m2]
    from v2 av(2,3) have "is_measured_ftree m \<and> is_leveln_ftree (Suc n) m"
    apply(simp)
    done
    hence bv: "is_measured_ftree m2 \<and>
   is_measured_node b \<and> is_leveln_ftree (Suc n) m2 \<and> is_leveln_node (Suc n) b"
    using myiv Cons
    apply(simp)
    done
    with av(2,3) v2 show "is_measured_ftree s \<and>
          is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd"
    apply(auto simp add: deep_def nodeToDigit_inv)
    done
  qed
qed

lemma viewLn_list: " viewLn t = Some (nd, s) 
  \<Longrightarrow> toList t = (nodeToList nd) @ (toList s)"
  apply(induct t arbitrary: nd s rule: viewLn.induct)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp add: deep_def)
  apply(auto simp add: toList_def)[1]
  apply(simp)
  apply(simp add: deep_def)
  apply(auto simp add: toList_def)[1]
  apply(simp)
  apply(simp add: deep_def)
  apply(auto simp add: toList_def)[1]
  apply(simp)
  subgoal premises prems for a m sf nd s
    using prems
  proof (cases "viewLn m" rule: viewnres_cases)
    case Nil
    hence av: "m = Empty" by (metis viewLn_empty)  
    from av prems
    show "nodeToList a @ toList m @ digitToList sf = nodeToList nd @ toList s"
      by (auto simp add: digitToTree_list)
  next        
    case (Cons b m2)
    with prems have bv: "nd = a" "s = (deep (nodeToDigit b) m2 sf)"
      by (auto simp add: deep_def)
    with Cons prems
    show "nodeToList a @ toList m @ digitToList sf = nodeToList nd @ toList s"
      apply(simp)
      apply(simp add: deep_def)
      apply(simp add: deep_def nodeToDigit_list)
      done
  qed
  done

lemma viewRn_empty: "t \<noteq> Empty \<longleftrightarrow> (viewRn t) \<noteq> None"
proof (cases t)
  case Empty thus ?thesis by simp
next
  case (Single Node) thus ?thesis by simp
next
  case (Deep a l x r) thus ?thesis 
  apply(auto)
  apply(case_tac r)
  apply(auto)
  apply(cases "viewRn x")
  apply(auto)
  done
qed

lemma viewRn_inv: "\<lbrakk>
  is_measured_ftree t; is_leveln_ftree n t; viewRn t = Some (nd, s)
  \<rbrakk> \<Longrightarrow> is_measured_ftree s \<and> is_measured_node nd \<and> 
       is_leveln_ftree n s \<and> is_leveln_node n nd"
  apply(induct t arbitrary: n nd s rule: viewRn.induct)
  apply(simp add: viewRn_empty)
  apply(simp)
  apply(auto simp add: deep_def)[1]
  apply(auto simp add: deep_def)[1]
  apply(auto simp add: deep_def)[1]
proof -
  fix ux a m "pr" n nd s
  assume av: "\<And>n nd s.
           \<lbrakk>is_measured_ftree m; is_leveln_ftree n m; viewRn m = Some (nd, s)\<rbrakk>
           \<Longrightarrow> is_measured_ftree s \<and>
              is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd "
         " is_measured_ftree (Deep ux pr m (One a)) "
         "is_leveln_ftree n (Deep ux pr m (One a))"
         "viewRn (Deep ux pr m (One a)) = Some (nd, s)"
  thus "is_measured_ftree s \<and>
          is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd"
  proof (cases "viewRn m" rule: viewnres_cases)
    case Nil
    with av(4) have v1: "nd = a" "s = digitToTree pr"
    by auto
    from v1 av(2,3) show "is_measured_ftree s \<and>
       is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd"
       apply(auto)
       apply(auto simp add: digitToTree_inv)
    done
  next
    case (Cons b m2)
    with av(4) have v2: "nd = a" "s = (deep pr m2 (nodeToDigit b))" 
    apply (auto simp add: deep_def)
    done
    note myiv = av(1)[of "Suc n" b m2]
    from v2 av(2,3) have "is_measured_ftree m \<and> is_leveln_ftree (Suc n) m"
    apply(simp)
    done
    hence bv: "is_measured_ftree m2 \<and>
   is_measured_node b \<and> is_leveln_ftree (Suc n) m2 \<and> is_leveln_node (Suc n) b"
    using myiv Cons
    apply(simp)
    done
    with av(2,3) v2 show "is_measured_ftree s \<and>
          is_measured_node nd \<and> is_leveln_ftree n s \<and> is_leveln_node n nd"
    apply(auto simp add: deep_def nodeToDigit_inv)
    done
  qed
qed

lemma viewRn_list: "viewRn t = Some (nd, s) 
  \<Longrightarrow> toList t = (toList s) @ (nodeToList nd)"
  apply(induct t arbitrary: nd s rule: viewRn.induct)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(simp add: deep_def)
  apply(auto simp add: toList_def)[1]
  apply(simp)
  apply(simp add: deep_def)
  apply(auto simp add: toList_def)[1]
  apply(simp)
  apply(simp add: deep_def)
  apply(auto simp add: toList_def)[1]
  apply(simp)
  subgoal premises prems for pr m a nd s
  proof (cases "viewRn m" rule: viewnres_cases)
    case Nil
    from Nil have av: "m = Empty" by (metis viewRn_empty)  
    from av prems
    show "digitToList pr @ toList m @ nodeToList a = toList s @ nodeToList nd"
      by (auto simp add: digitToTree_list)
  next        
    case (Cons b m2)
    with prems have bv: "nd = a" "s = (deep pr m2 (nodeToDigit b))"
    apply(auto simp add: deep_def) done
    with Cons prems
    show "digitToList pr @ toList m @ nodeToList a = toList s @ nodeToList nd"
      apply(simp)
      apply(simp add: deep_def)
      apply(simp add: deep_def nodeToDigit_list)
     done
  qed
  done


type_synonym ('e,'a) viewres = "(('e \<times>'a) \<times> ('e,'a) FingerTreeStruc) option"

text \<open>Detach the leftmost element. Return @{const None} on empty finger tree.\<close>
definition viewL :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) viewres" 
  where 
"viewL t = (case viewLn t of 
  None \<Rightarrow> None |
  (Some (a, t2)) \<Rightarrow> Some ((n_unwrap a), t2))"

lemma viewL_correct: 
  assumes INV: "ft_invar t" 
  shows
  "(t=Empty \<Longrightarrow> viewL t = None)"
  "(t\<noteq>Empty \<Longrightarrow> (\<exists>a s. viewL t = Some (a, s) \<and> ft_invar s 
                        \<and> toList t = a # toList s))"
proof -
  assume "t=Empty" thus "viewL t = None" by (simp add: viewL_def)
next
  assume NE: "t \<noteq> Empty"
  from INV have INV': "is_leveln_ftree 0 t" "is_measured_ftree t" 
    by (simp_all add: ft_invar_def)
  from NE have v1: "viewLn t \<noteq> None" by (auto simp add: viewLn_empty)
  then obtain nd s where vn: "viewLn t = Some (nd, s)" 
    by (cases "viewLn t") (auto)
  from this obtain a where v1: "viewL t = Some (a, s)"
    by (auto simp add: viewL_def)
  from INV' vn have 
    v2: "is_measured_ftree s \<and> is_leveln_ftree 0 s 
         \<and> is_leveln_node 0 nd \<and> is_measured_node nd"
        "toList t = (nodeToList nd) @ (toList s)"
    by (auto simp add: viewLn_inv[of t 0 nd s] viewLn_list[of t])
  with v1 vn have v3: "nodeToList nd = [a]"
    apply (auto simp add: viewL_def )
    apply (induct nd)
    apply auto
    done
  with v1 v2
  show "\<exists>a s. viewL t = Some (a, s) \<and> ft_invar s \<and> toList t = a # toList s"
    by (auto simp add: ft_invar_def)
qed

lemma viewL_correct_empty[simp]: "viewL Empty = None"
  by (simp add: viewL_def)

lemma viewL_correct_nonEmpty: 
  assumes "ft_invar t" "t \<noteq> Empty" 
  obtains a s where 
  "viewL t = Some (a, s)" "ft_invar s" "toList t = a # toList s"
  using assms viewL_correct by blast


text \<open>Detach the rightmost element. Return @{const None} on empty finger tree.\<close>
definition viewR :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) viewres" 
  where 
  "viewR t = (case viewRn t of 
    None \<Rightarrow> None |
    (Some (a, t2)) \<Rightarrow> Some ((n_unwrap a), t2))"

lemma viewR_correct: 
  assumes INV: "ft_invar t"
  shows
  "(t = Empty \<Longrightarrow> viewR t = None)"
  "(t \<noteq> Empty \<Longrightarrow> (\<exists> a s. viewR t = Some (a, s) \<and> ft_invar s 
                          \<and> toList t = toList s @ [a]))"
proof -
  assume "t=Empty" thus "viewR t = None" by (simp add: viewR_def)
next
  assume NE: "t \<noteq> Empty"
  from INV have INV': "is_leveln_ftree 0 t" "is_measured_ftree t" 
    unfolding ft_invar_def by simp_all
  from NE have v1: "viewRn t \<noteq> None" by (auto simp add: viewRn_empty)
  then obtain nd s where vn: "viewRn t = Some (nd, s)" 
    by (cases "viewRn t") (auto)
  from this obtain a where v1: "viewR t = Some (a, s)"
    by (auto simp add: viewR_def)
  from INV' vn have 
    v2: "is_measured_ftree s \<and> is_leveln_ftree 0 s 
         \<and> is_leveln_node 0 nd \<and> is_measured_node nd"
        "toList t = (toList s) @ (nodeToList nd)"
    by (auto simp add: viewRn_inv[of t 0 nd s] viewRn_list[of t])
  with v1 vn have v3: "nodeToList nd = [a]"
    apply (auto simp add: viewR_def )
    apply (induct nd)
    apply auto
    done
  with v1 v2
  show "\<exists>a s. viewR t = Some (a, s) \<and> ft_invar s \<and> toList t = toList s @ [a]"
    unfolding ft_invar_def by auto
qed  

lemma viewR_correct_empty[simp]: "viewR Empty = None"
  unfolding viewR_def by simp

lemma viewR_correct_nonEmpty: 
  assumes "ft_invar t" "t \<noteq> Empty" 
  obtains a s where 
  "viewR t = Some (a, s)" "ft_invar s \<and> toList t = toList s @ [a]"
  using assms viewR_correct by blast

text \<open>Finger trees viewed as a double-ended queue. The head and tail functions
  here are only
  defined for non-empty queues, while the view-functions were also defined for
  empty finger trees.\<close>
text "Check for emptiness"
definition isEmpty :: "('e,'a) FingerTreeStruc \<Rightarrow> bool" where
  [code del]: "isEmpty t = (t = Empty)"
lemma isEmpty_correct: "isEmpty t \<longleftrightarrow> toList t = []"
  unfolding isEmpty_def by (simp add: toList_empty)
\<comment> \<open>Avoid comparison with @{text "(=)"}, and thus unnecessary equality-class
    parameter on element types in generated code\<close>
lemma [code]: "isEmpty t = (case t of Empty \<Rightarrow> True | _ \<Rightarrow> False)"
  apply (cases t)
  apply (auto simp add: isEmpty_def)
  done

text "Leftmost element"
definition head :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> 'e \<times> 'a" where
  "head t = (case viewL t of (Some (a, _)) \<Rightarrow> a)"
lemma head_correct:
  assumes "ft_invar t" "t \<noteq> Empty" 
  shows "head t = hd (toList t)"
proof -
  from assms viewL_correct 
  obtain a s where 
    v1:"viewL t = Some (a, s) \<and> ft_invar s \<and> toList t = a # toList s" by blast
  hence v2: "head t = a" by (auto simp add: head_def)
  from v1 have "hd (toList t) = a" by simp
  with v2 show ?thesis by simp
qed

text "All but the leftmost element"
definition tail 
  :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) FingerTreeStruc" 
  where
  "tail t = (case viewL t of (Some (_, m)) \<Rightarrow> m)"
lemma tail_correct: 
  assumes "ft_invar t" "t \<noteq> Empty" 
  shows "toList (tail t) = tl (toList t)" and "ft_invar (tail t)"
proof -
  from assms viewL_correct 
  obtain a s where 
    v1:"viewL t = Some (a, s) \<and> ft_invar s \<and> toList t = a # toList s" by blast
  hence v2: "tail t = s" by (auto simp add: tail_def)
  from v1 have "tl (toList t) = toList s" by simp
  with v1 v2 show 
    "toList (tail t) = tl (toList t)" 
    "ft_invar (tail t)"
    by simp_all
qed

text "Rightmost element"  
definition headR :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> 'e \<times> 'a" where
  "headR t = (case viewR t of (Some (a, _)) \<Rightarrow> a)"
lemma headR_correct:
  assumes "ft_invar t" "t \<noteq> Empty" 
  shows  "headR t = last (toList t)"
proof -
  from assms viewR_correct 
  obtain a s where 
    v1:"viewR t = Some (a, s) \<and> ft_invar s \<and> toList t = toList s @ [a]" by blast
  hence v2: "headR t = a" by (auto simp add: headR_def)
  with v1 show ?thesis by auto
qed

text "All but the rightmost element"
definition tailR 
  :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) FingerTreeStruc" 
  where
  "tailR t = (case viewR t of (Some (_, m)) \<Rightarrow> m)"
lemma tailR_correct: 
  assumes "ft_invar t" "t \<noteq> Empty"
  shows "toList (tailR t) = butlast (toList t)" and "ft_invar (tailR t)"
proof -
  from assms viewR_correct 
  obtain a s where 
    v1:"viewR t = Some (a, s) \<and> ft_invar s \<and> toList t = toList s @ [a]" by blast
  hence v2: "tailR t = s" by (auto simp add: tailR_def)
  with v1 show "toList (tailR t) = butlast (toList t)" and "ft_invar (tailR t)"
    by auto
qed 

subsubsection \<open>Concatenation\<close>
primrec lconsNlist :: "('e,'a::monoid_add) Node list 
    \<Rightarrow> ('e,'a) FingerTreeStruc \<Rightarrow> ('e,'a) FingerTreeStruc" where
  "lconsNlist [] t = t" |
  "lconsNlist (x#xs) t = nlcons x (lconsNlist xs t)"
primrec rconsNlist :: "('e,'a::monoid_add) FingerTreeStruc 
    \<Rightarrow> ('e,'a) Node list \<Rightarrow> ('e,'a) FingerTreeStruc" where
  "rconsNlist t []  = t" |
  "rconsNlist t (x#xs)  = rconsNlist (nrcons t x) xs"

fun nodes :: "('e,'a::monoid_add) Node list  \<Rightarrow> ('e,'a) Node list" where
  "nodes [a, b] = [node2 a b]" |
  "nodes [a, b, c] = [node3 a b c]" |
  "nodes [a,b,c,d] = [node2 a b, node2 c d]" |
  "nodes (a#b#c#xs) = (node3 a b c) # (nodes xs)"


text \<open>Recursively we concatenate two FingerTreeStrucs while we keep the 
  inner Nodes in a list\<close>
fun app3 :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) Node list 
    \<Rightarrow> ('e,'a) FingerTreeStruc \<Rightarrow> ('e,'a) FingerTreeStruc" where
  "app3 Empty xs t = lconsNlist xs t" |
  "app3 t xs Empty = rconsNlist t xs" |
  "app3 (Single x) xs t = nlcons x (lconsNlist xs t)" |
  "app3 t xs (Single x) = nrcons (rconsNlist t xs) x" |
  "app3 (Deep _ pr1 m1 sf1) ts (Deep _ pr2 m2 sf2) =
    deep pr1 (app3 m1 
      (nodes ((digitToNlist sf1) @ ts @ (digitToNlist pr2))) m2) sf2"

lemma lconsNlist_inv:
  assumes "is_leveln_ftree n t" 
  and "is_measured_ftree t"
  and "\<forall> x\<in>set xs. (is_leveln_node n x \<and> is_measured_node x)"
  shows 
  "is_leveln_ftree n (lconsNlist xs t) \<and> is_measured_ftree (lconsNlist xs t)"
  by (insert assms, induct xs, auto simp add: nlcons_invlevel nlcons_invmeas)

lemma rconsNlist_inv:
  assumes "is_leveln_ftree n t" 
  and "is_measured_ftree t"
  and "\<forall> x\<in>set xs. (is_leveln_node n x \<and> is_measured_node x)"
  shows 
  "is_leveln_ftree n (rconsNlist t xs) \<and> is_measured_ftree (rconsNlist t xs)"
  by (insert assms, induct xs arbitrary: t, 
      auto simp add: nrcons_invlevel nrcons_invmeas)

lemma nodes_inv:
  assumes "\<forall> x \<in> set ts. is_leveln_node n x \<and> is_measured_node x"
  and "length ts \<ge> 2"
  shows "\<forall> x \<in> set (nodes ts). is_leveln_node (Suc n) x \<and> is_measured_node x"
proof (insert assms, induct ts rule: nodes.induct)
  case (1 a b)
  thus ?case by (simp add: node2_def)
next
  case (2 a b c)
  thus ?case by (simp add: node3_def)
next
  case (3 a b c d)
  thus ?case by (simp add: node2_def)
next
  case (4 a b c v vb vc)
  thus ?case by (simp add: node3_def)
next
  show "\<lbrakk>\<forall>x\<in>set []. is_leveln_node n x \<and> is_measured_node x; 2 \<le> length []\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>set (nodes []). is_leveln_node (Suc n) x \<and> is_measured_node x" 
    by  simp
next
  show 
    "\<And>v. \<lbrakk>\<forall>x\<in>set [v]. is_leveln_node n x \<and> is_measured_node x; 2 \<le> length [v]\<rbrakk>
    \<Longrightarrow> \<forall>x\<in>set (nodes [v]). is_leveln_node (Suc n) x \<and> is_measured_node x" 
    by simp
qed

lemma nodes_inv2:
  assumes "is_leveln_digit n sf1"
  and "is_measured_digit sf1"
  and "is_leveln_digit n pr2"
  and "is_measured_digit pr2"
  and "\<forall> x \<in> set ts. is_leveln_node n x \<and> is_measured_node x"
  shows 
  "\<forall>x\<in>set (nodes (digitToNlist sf1 @ ts @ digitToNlist pr2)).
                is_leveln_node (Suc n) x \<and> is_measured_node x" 
proof -
  have v1:" \<forall>x\<in>set (digitToNlist sf1 @ ts @ digitToNlist pr2). 
                 is_leveln_node n x \<and> is_measured_node x" 
    using assms
    apply (simp add: digitToNlist_def)
    apply (cases sf1)
    apply (cases pr2)
    apply simp_all
    apply (cases pr2)
    apply (simp_all)
    apply (cases pr2)
    apply (simp_all)
    apply (cases pr2)
    apply (simp_all)
    done
  have v2: "length (digitToNlist sf1 @ ts @ digitToNlist pr2) \<ge> 2"
    apply (cases sf1)
    apply (cases pr2)
    apply simp_all
    done
  thus ?thesis 
    using v1 nodes_inv[of "digitToNlist sf1 @ ts @ digitToNlist pr2"] 
    by blast
qed

lemma app3_inv:
  assumes "is_leveln_ftree n t1"
  and "is_leveln_ftree n t2"
  and "is_measured_ftree t1"
  and "is_measured_ftree t2"
  and "\<forall> x\<in>set xs. (is_leveln_node n x \<and> is_measured_node x)"
  shows "is_leveln_ftree n (app3 t1 xs t2) \<and> is_measured_ftree (app3 t1 xs t2)"
proof (insert assms, induct t1 xs t2 arbitrary: n rule: app3.induct)
  case (1 xs t n)
  thus ?case using lconsNlist_inv by simp
next
  case "2_1" 
  thus ?case by (simp add: rconsNlist_inv)
next
  case "2_2"
  thus ?case by (simp add: lconsNlist_inv rconsNlist_inv)
next
  case "3_1"
  thus ?case by (simp add: lconsNlist_inv nlcons_invlevel nlcons_invmeas )
next
  case "3_2"
  thus ?case 
    by (simp only: app3.simps) 
       (simp add: lconsNlist_inv nlcons_invlevel nlcons_invmeas)
next
  case 4
  thus ?case 
    by (simp only: app3.simps)
       (simp add: rconsNlist_inv nrcons_invlevel nrcons_invmeas)
next
  case (5 uu pr1 m1 sf1 ts uv pr2 m2 sf2 n)
  thus ?case
  proof -
    have v1: "is_leveln_ftree (Suc n) m1" 
      and v2: "is_leveln_ftree (Suc n) m2"
      using "5.prems" by (simp_all add: is_leveln_ftree_def)
    have v3: "is_measured_ftree m1" 
      and v4: "is_measured_ftree m2"
      using "5.prems" by (simp_all add: is_measured_ftree_def)
    have v5: "is_leveln_digit n sf1"
      "is_measured_digit sf1"
      "is_leveln_digit n pr2"
      "is_measured_digit pr2"
      "\<forall>x\<in>set ts. is_leveln_node n x \<and> is_measured_node x"
      using "5.prems"
      by (simp_all add: is_leveln_ftree_def is_measured_ftree_def)
    note v6 = nodes_inv2[OF v5]
    note v7 = "5.hyps"[OF v1 v2 v3 v4 v6]
    have v8: "is_leveln_digit n sf2"
      "is_measured_digit sf2"
      "is_leveln_digit n pr1"
      "is_measured_digit pr1"
      using "5.prems"
      by (simp_all add: is_leveln_ftree_def is_measured_ftree_def)
    
    show ?thesis using v7 v8
      by (simp add: is_leveln_ftree_def is_measured_ftree_def deep_def)
  qed
qed

primrec nlistToList:: "(('e, 'a) Node) list \<Rightarrow> ('e \<times> 'a) list" where
  "nlistToList [] = []"|
  "nlistToList (x#xs) = (nodeToList x) @ (nlistToList xs)"

lemma nodes_list: "length xs \<ge> 2 \<Longrightarrow> nlistToList (nodes xs) = nlistToList xs"
  by (induct xs rule: nodes.induct) (auto simp add: node2_def node3_def)

lemma nlistToList_app: 
  "nlistToList (xs@ys) = (nlistToList xs) @ (nlistToList ys)"
  by (induct xs arbitrary: ys, simp_all)

lemma nlistListLCons: "toList (lconsNlist xs t) = (nlistToList xs) @ (toList t)"
  by (induct xs) (auto simp add: nlcons_list)
 
lemma nlistListRCons: "toList (rconsNlist t xs) = (toList t) @ (nlistToList xs)"
  by (induct xs arbitrary: t) (auto simp add: nrcons_list)

lemma app3_list_lem1: 
  "nlistToList (nodes (digitToNlist sf1 @ ts @ digitToNlist pr2)) =
       digitToList sf1 @ nlistToList ts @ digitToList pr2"
proof -
  have len1: "length (digitToNlist sf1 @ ts @ digitToNlist pr2) \<ge> 2"
    by (cases sf1,cases pr2,simp_all)
  
  have "(nlistToList (digitToNlist sf1 @ ts @ digitToNlist pr2)) 
       = (digitToList sf1 @ nlistToList ts @ digitToList pr2)"
    apply (cases sf1, cases pr2) 
    apply (simp_all add: nlistToList_app)
    apply (cases pr2, auto)
    apply (cases pr2, auto)
    apply (cases pr2, auto)
    done
  with nodes_list[OF len1] show ?thesis by simp
qed


lemma app3_list: 
  "toList (app3 t1 xs t2) = (toList t1) @ (nlistToList xs) @ (toList t2)"
  apply (induct t1 xs t2 rule: app3.induct)
  apply (simp_all add: nlistListLCons nlistListRCons nlcons_list nrcons_list)
  apply (simp add: app3_list_lem1 deep_def)
  done


definition app 
  :: "('e,'a::monoid_add) FingerTreeStruc \<Rightarrow> ('e,'a) FingerTreeStruc 
       \<Rightarrow> ('e,'a) FingerTreeStruc" 
  where "app t1 t2 = app3 t1 [] t2"

lemma app_correct: 
  assumes "ft_invar t1" "ft_invar t2" 
  shows "toList (app t1 t2) = (toList t1) @ (toList t2)" 
    and "ft_invar (app t1 t2)"
  using assms
  by (auto simp add: app3_inv app3_list ft_invar_def app_def)

lemma app_inv: "\<lbrakk>ft_invar t1;ft_invar t2\<rbrakk> \<Longrightarrow> ft_invar (app t1 t2)"
  by (auto simp add: app3_inv ft_invar_def app_def)

lemma app_list[simp]: "toList (app t1 t2) = (toList t1) @ (toList t2)"
  by (simp add: app3_list app_def)


subsubsection "Splitting"

type_synonym ('e,'a) SplitDigit = 
  "('e,'a) Node list  \<times> ('e,'a) Node \<times> ('e,'a) Node list"
type_synonym ('e,'a) SplitTree  = 
  "('e,'a) FingerTreeStruc \<times> ('e,'a) Node \<times> ('e,'a) FingerTreeStruc"

  text \<open>Auxiliary functions to create a correct finger tree 
    even if the left or right digit is empty\<close> 
fun deepL :: "('e,'a::monoid_add) Node list \<Rightarrow> ('e,'a) FingerTreeStruc 
    \<Rightarrow> ('e,'a) Digit \<Rightarrow> ('e,'a) FingerTreeStruc" where
  "deepL [] m sf = (case (viewLn m) of None \<Rightarrow> digitToTree sf |
                                 (Some (a, m2)) \<Rightarrow> deep (nodeToDigit a) m2 sf)" |
  "deepL pr m sf = deep (nlistToDigit pr) m sf"
fun deepR :: "('e,'a::monoid_add) Digit \<Rightarrow> ('e,'a) FingerTreeStruc 
    \<Rightarrow> ('e,'a) Node list \<Rightarrow> ('e,'a) FingerTreeStruc" where
  "deepR pr m [] = (case (viewRn m) of None \<Rightarrow> digitToTree pr |
                                 (Some (a, m2)) \<Rightarrow> deep pr m2 (nodeToDigit a))" |
  "deepR pr m sf = deep pr m (nlistToDigit sf)"

  text \<open>Splitting a list of nodes\<close>
fun splitNlist :: "('a::monoid_add \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('e,'a) Node list 
    \<Rightarrow> ('e,'a) SplitDigit" where
  "splitNlist p i [a]   = ([],a,[])" |
  "splitNlist p i (a#b) = 
    (let i2 = (i + gmn a) in 
      (if (p i2) 
        then ([],a,b) 
        else 
         (let (l,x,r) = (splitNlist p i2 b) in ((a#l),x,r))))" 

  text \<open>Splitting a digit by converting it into a list of nodes\<close>
definition splitDigit :: "('a::monoid_add \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('e,'a) Digit 
    \<Rightarrow> ('e,'a) SplitDigit" where
  "splitDigit p i d = splitNlist p i (digitToNlist d)" 

  text \<open>Creating a finger tree from list of nodes\<close>
definition nlistToTree :: "('e,'a::monoid_add) Node list 
    \<Rightarrow> ('e,'a) FingerTreeStruc" where 
  "nlistToTree xs = lconsNlist xs Empty"

    text \<open>Recursive splitting into a left and right tree and a center node\<close>
fun nsplitTree :: "('a::monoid_add \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('e,'a) FingerTreeStruc 
    \<Rightarrow> ('e,'a) SplitTree" where
  "nsplitTree p i Empty = (Empty, Tip undefined undefined, Empty)" 
      \<comment> \<open>Making the function total\<close> |
  "nsplitTree p i (Single ea) = (Empty,ea,Empty)" |
  "nsplitTree p i (Deep _ pr m sf) = 
     (let 
       vpr = (i + gmd pr); 
       vm = (vpr + gmft m) 
      in 
        if (p vpr) then 
          (let (l,x,r) = (splitDigit p i pr) in 
            (nlistToTree l,x,deepL r m sf)) 
        else (if (p vm) then 
          (let (ml,xs,mr) = (nsplitTree p vpr m); 
            (l,x,r) = (splitDigit p (vpr + gmft ml) (nodeToDigit xs)) in
              (deepR pr ml l,x,deepL r mr sf))
        else 
          (let (l,x,r) = (splitDigit p vm sf) in 
            (deepR pr m l,x,nlistToTree r))    
      ))"


lemma nlistToTree_inv: 
  "\<forall> x \<in> set nl. is_measured_node x \<Longrightarrow> is_measured_ftree (nlistToTree nl)"
  "\<forall> x \<in> set nl. is_leveln_node n x \<Longrightarrow> is_leveln_ftree n (nlistToTree nl)"
  by (unfold nlistToTree_def, induct nl, auto simp add: nlcons_invmeas)
     (induct nl, auto simp add: nlcons_invlevel)

lemma nlistToTree_list: "toList (nlistToTree nl) = nlistToList nl"
  by (auto simp add: nlistToTree_def nlistListLCons)

lemma deepL_inv:
  assumes "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
  and "is_leveln_digit n sf \<and> is_measured_digit sf"
  and "\<forall> x \<in> set pr. (is_measured_node x \<and> is_leveln_node n x) \<and> length pr \<le> 4"
  shows  "is_leveln_ftree n (deepL pr m sf) \<and> is_measured_ftree (deepL pr m sf)"
  apply (insert assms)
  apply (induct "pr" m sf rule: deepL.induct)
  apply (simp split: viewnres_split)
  apply auto[1]
  apply (simp_all add: digitToTree_inv deep_def)
proof -
  fix m sf Node FingerTreeStruc
  assume "is_leveln_ftree (Suc n) m" "is_measured_ftree m" 
         "is_leveln_digit n sf" "is_measured_digit sf" 
         "viewLn m = Some (Node, FingerTreeStruc)"
  thus "is_leveln_digit n (nodeToDigit Node) 
        \<and> is_leveln_ftree (Suc n) FingerTreeStruc"
    by (simp add: viewLn_inv[of m "Suc n" Node FingerTreeStruc] nodeToDigit_inv)
next
  fix m sf Node FingerTreeStruc
  assume assms1: 
    "is_leveln_ftree (Suc n) m" "is_measured_ftree m" 
    "is_leveln_digit n sf" "is_measured_digit sf" 
    "viewLn m = Some (Node, FingerTreeStruc)"
  thus "is_measured_digit (nodeToDigit Node) \<and> is_measured_ftree FingerTreeStruc"
    apply (auto simp only: viewLn_inv[of m "Suc n" Node FingerTreeStruc])
  proof -
    from assms1 have "is_measured_node Node \<and> is_leveln_node (Suc n) Node" 
      by (simp add: viewLn_inv[of m "Suc n" Node FingerTreeStruc])
    thus "is_measured_digit (nodeToDigit Node)" 
      by (auto simp add: nodeToDigit_inv)
  qed
next
  fix v va
  assume 
    "is_measured_node v \<and> is_leveln_node n (v:: ('a,'b) Node) \<and>
    length  (va::('a, 'b) Node list) \<le> 3 \<and> 
    (\<forall>x\<in>set va. is_measured_node x \<and> is_leveln_node n x \<and> length va \<le> 3)"
  thus "is_leveln_digit n (nlistToDigit (v # va)) 
       \<and> is_measured_digit (nlistToDigit (v # va))"
    by(cases "v#va" rule: nlistToDigit.cases,simp_all)
qed

(*corollary deepL_inv':
  assumes "is_leveln_ftree (Suc n) m" "is_measured_ftree m"
  and "is_leveln_digit n sf" "is_measured_digit sf"
  and "\<forall> x \<in> set pr. (is_measured_node x \<and> is_leveln_node n x)" "length pr \<le> 4"
  shows  "is_leveln_ftree n (deepL pr m sf)" "is_measured_ftree (deepL pr m sf)"
  using assms deepL_inv by blast+
*)
            
lemma nlistToDigit_list:
  assumes "1 \<le> length xs \<and> length xs \<le> 4"
  shows "digitToList(nlistToDigit xs) = nlistToList xs" 
  by (insert assms, cases xs rule: nlistToDigit.cases,auto)

lemma deepL_list:
  assumes "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
  and "is_leveln_digit n sf \<and> is_measured_digit sf"
  and "\<forall> x \<in> set pr. (is_measured_node x \<and> is_leveln_node n x) \<and> length pr \<le> 4"
  shows "toList (deepL pr m sf) = nlistToList pr @ toList m @ digitToList sf"
proof (insert assms, induct "pr" m sf rule: deepL.induct)
  case (1 m sf)
  thus ?case
  proof (auto split: viewnres_split simp add: deep_def)
    assume "viewLn m = None"
    hence "m = Empty" by (metis viewLn_empty)
    hence "toList m = []" by simp
    thus "toList (digitToTree sf) = toList m @ digitToList sf" 
      by (simp add:digitToTree_list)
  next
    fix nd t
    assume "viewLn m = Some (nd, t)" 
      "is_leveln_ftree (Suc n) m" "is_measured_ftree m"
    hence "nodeToList nd @ toList t = toList m" by (metis viewLn_list)
    thus "digitToList (nodeToDigit nd) @ toList t = toList m"
      by (simp add: nodeToDigit_list)
  qed
next
  case (2 v va m sf)
  thus ?case
    apply (unfold deepL.simps)
    apply (simp add: deep_def)
    apply (simp add: nlistToDigit_list)
    done
qed
  
lemma deepR_inv:
  assumes "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
  and "is_leveln_digit n pr \<and> is_measured_digit pr"
  and "\<forall> x \<in> set sf. (is_measured_node x \<and> is_leveln_node n x) \<and> length sf \<le> 4"
  shows "is_leveln_ftree n (deepR pr m sf) \<and> is_measured_ftree (deepR pr m sf)"
  apply (insert assms)
  apply (induct "pr" m sf rule: deepR.induct)
  apply (simp split: viewnres_split)
  apply auto[1]
  apply (simp_all add: digitToTree_inv deep_def)
proof -
  fix m "pr" Node FingerTreeStruc  
  assume "is_leveln_ftree (Suc n) m" "is_measured_ftree m" 
         "is_leveln_digit n pr" "is_measured_digit pr"
         "viewRn m = Some (Node, FingerTreeStruc)"
  thus 
    "is_leveln_digit n (nodeToDigit Node) 
    \<and> is_leveln_ftree (Suc n) FingerTreeStruc"
    by (simp add: viewRn_inv[of m "Suc n" Node FingerTreeStruc] nodeToDigit_inv)
next
  fix m "pr" Node FingerTreeStruc
  assume assms1: 
    "is_leveln_ftree (Suc n) m" "is_measured_ftree m" 
    "is_leveln_digit n pr" "is_measured_digit pr" 
    "viewRn m = Some (Node, FingerTreeStruc)"
  thus "is_measured_ftree FingerTreeStruc \<and> is_measured_digit (nodeToDigit Node)"
    apply (auto simp only: viewRn_inv[of m "Suc n" Node FingerTreeStruc])
  proof -
    from assms1 have "is_measured_node Node \<and> is_leveln_node (Suc n) Node" 
      by (simp add: viewRn_inv[of m "Suc n" Node FingerTreeStruc])
    thus "is_measured_digit (nodeToDigit Node)" 
      by (auto simp add: nodeToDigit_inv)
  qed
next
  fix v va
  assume 
    "is_measured_node v \<and> is_leveln_node n (v:: ('a,'b) Node) \<and>
    length  (va::('a, 'b) Node list) \<le> 3 \<and> 
    (\<forall>x\<in>set va. is_measured_node x \<and> is_leveln_node n x \<and> length va \<le> 3)"
  thus "is_leveln_digit n (nlistToDigit (v # va)) \<and> 
        is_measured_digit (nlistToDigit (v # va))"
    by(cases "v#va" rule: nlistToDigit.cases,simp_all)
qed
           

lemma deepR_list:
  assumes "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
  and "is_leveln_digit n pr \<and> is_measured_digit pr"
  and "\<forall> x \<in> set sf. (is_measured_node x \<and> is_leveln_node n x) \<and> length sf \<le> 4"
  shows "toList (deepR pr m sf) = digitToList pr @ toList m @ nlistToList sf"
proof (insert assms, induct "pr" m sf rule: deepR.induct)
  case (1 "pr" m)
  thus ?case
  proof (auto split: viewnres_split simp add: deep_def)
    assume "viewRn m = None"
    hence "m = Empty" by (metis viewRn_empty)
    hence "toList m = []" by simp
    thus "toList (digitToTree pr) = digitToList pr @ toList m"
      by (simp add:digitToTree_list)
  next
    fix nd t
    assume "viewRn m = Some (nd, t)" "is_leveln_ftree (Suc n) m" 
           "is_measured_ftree m"
    hence "toList t @ nodeToList nd = toList m" by (metis viewRn_list)
    thus "toList t @ digitToList (nodeToDigit nd) = toList m"
      by (simp add: nodeToDigit_list)
  qed
next
  case (2 "pr" m v va)
  thus ?case
    apply (unfold deepR.simps)
    apply (simp add: deep_def)
    apply (simp add: nlistToDigit_list)
    done
qed

primrec gmnl:: "('e, 'a::monoid_add) Node list \<Rightarrow> 'a" where
"gmnl [] = 0"|
"gmnl (x#xs) = gmn x + gmnl xs"

lemma gmnl_correct:
  assumes "\<forall> x \<in> set xs. is_measured_node x"
  shows  "gmnl xs = sum_list (map snd (nlistToList xs))"
  by (insert assms, induct xs) (auto simp add: add.assoc gmn_correct)

lemma splitNlist_correct:" \<lbrakk>
  \<And>(a::'a) (b::'a). p a \<Longrightarrow> p (a + b);
  \<not> p i;
  p (i + gmnl (nl ::('e,'a::monoid_add) Node list));
  splitNlist p i nl = (l, n, r)
  \<rbrakk> \<Longrightarrow>  
  \<not> p (i + (gmnl l))
  \<and>
  p (i + (gmnl l) + (gmn n))
  \<and>
  nl = l @ n # r
  "
proof (induct p i nl arbitrary: l n r rule: splitNlist.induct)
  case 1 thus ?case by simp
next
  case (2 p i a v va l n r) note IV = this 
  show ?case
  proof (cases "p (i + (gmn a))")
    case True with IV show ?thesis by simp
  next
    case False note IV2 = this IV  thus ?thesis
    proof -
      obtain l1 n1 r1 where 
        v1[simp]: "splitNlist p (i + gmn a) (v # va) = (l1, n1, r1)" 
        by (cases "splitNlist p (i + gmn a) (v # va)", blast)
      note miv = IV2(2)[of "i + gmn a" l1 n1 r1]
      have v2:"p (i + gmn a + gmnl (v # va))" 
        using IV2(5) by (simp add: add.assoc)
      note miv2 =  miv[OF _ IV2(1) IV2(3) IV2(1)  v2 v1]
      have v3: "a # l1 = l" "n1 = n" "r1 = r"  using IV2 v1 by auto
      with miv2 have 
        v4: "\<not> p (i + gmn a + gmnl l1) \<and> 
             p (i + gmn a + gmnl l1 + gmn n1) \<and> 
             v # va = l1 @ n1 # r1"
        by auto
      with v2 v3 show ?thesis
        by (auto simp add: add.assoc)
    qed
  qed
next
  case 3 thus ?case by simp
qed

lemma digitToNlist_inv: 
  "is_measured_digit d \<Longrightarrow> (\<forall> x \<in> set (digitToNlist d). is_measured_node x)" 
  "is_leveln_digit n d \<Longrightarrow> (\<forall> x \<in> set (digitToNlist d). is_leveln_node n x)"
  by (cases d, auto)(cases d, auto)
  
lemma gmnl_gmd:
  "is_measured_digit d \<Longrightarrow> gmnl (digitToNlist d) = gmd d"
  by (cases d, auto simp add: add.assoc)
  
lemma gmn_gmd: 
  "is_measured_node nd \<Longrightarrow> gmd (nodeToDigit nd) = gmn nd"
  by (auto simp add: nodeToDigit_inv nodeToDigit_list gmn_correct gmd_correct)

lemma splitDigit_inv:
  "\<lbrakk>
  \<And>(a::'a) (b::'a). p a \<Longrightarrow> p (a + b);
  \<not> p i;
  is_measured_digit d;
  is_leveln_digit n d;
  p (i + gmd (d ::('e,'a::monoid_add) Digit));
  splitDigit p i d = (l, nd, r)
  \<rbrakk> \<Longrightarrow>  
  \<not> p (i + (gmnl l))
  \<and>
  p (i + (gmnl l) + (gmn nd))
  \<and>
  (\<forall> x \<in> set l. (is_measured_node x \<and> is_leveln_node n x))
  \<and>
  (\<forall> x \<in> set r. (is_measured_node x \<and> is_leveln_node n x))
  \<and>
  (is_measured_node nd \<and> is_leveln_node n nd )
  "
proof -
  fix p i d n l nd r
  assume assms: "\<And>a b. p a \<Longrightarrow> p (a + b)" "\<not> p i" "is_measured_digit d" 
    "p (i + gmd d)" "splitDigit p i d = (l, nd, r)"
    "is_leveln_digit n d"
  from assms(3, 4) have v1: "p (i + gmnl (digitToNlist d))" 
    by (simp add: gmnl_gmd)
  note snc = splitNlist_correct [of p i "digitToNlist d" l nd r]
  from assms(5) have v2: "splitNlist p i (digitToNlist d) = (l, nd, r)" 
    by (simp add: splitDigit_def)
  note snc1 = snc[OF assms(1) assms(2) v1 v2]
  hence v3: "\<not> p (i + gmnl l) \<and> p (i + gmnl l + gmn nd) \<and> 
             digitToNlist d = l @ nd # r" by auto
  from assms(3,6) have 
    v4:" \<forall> x \<in> set (digitToNlist d). is_measured_node x"
    " \<forall> x \<in> set (digitToNlist d). is_leveln_node n x"
    by(auto simp add: digitToNlist_inv)
  with v3 have v5: "\<forall> x \<in> set l. (is_measured_node x \<and> is_leveln_node n x)"
    "\<forall> x \<in> set r. (is_measured_node x \<and> is_leveln_node n x)"
    "is_measured_node nd \<and> is_leveln_node n nd" by auto
  with v3 v5 show 
    "\<not> p (i + gmnl l) \<and> p (i + gmnl l + gmn nd) \<and> 
    (\<forall>x\<in>set l. is_measured_node x \<and> is_leveln_node n x) \<and> 
    (\<forall>x\<in>set r. is_measured_node x \<and> is_leveln_node n x) \<and> 
    is_measured_node nd \<and> is_leveln_node n nd"
    by auto
qed


lemma splitDigit_inv':
  "\<lbrakk>
  splitDigit p i d = (l, nd, r);
  is_measured_digit d;
  is_leveln_digit n d
  \<rbrakk> \<Longrightarrow>  
  (\<forall> x \<in> set l. (is_measured_node x \<and> is_leveln_node n x))
  \<and>
  (\<forall> x \<in> set r. (is_measured_node x \<and> is_leveln_node n x))
  \<and>
  (is_measured_node nd \<and> is_leveln_node n nd )
  "
  apply (unfold splitDigit_def)
  apply (cases d)
  apply (auto split: if_split_asm simp add: Let_def)
  done


lemma splitDigit_list: "splitDigit p i d = (l,n,r) \<Longrightarrow> 
  (digitToList d) = (nlistToList l) @ (nodeToList n) @ (nlistToList r)
  \<and> length l \<le> 4 \<and> length r \<le> 4"
  apply (unfold splitDigit_def)
  apply (cases d)
  apply (auto split: if_split_asm simp add: Let_def)
  done

lemma gmnl_gmft: "\<forall> x \<in> set nl. is_measured_node x \<Longrightarrow> 
  gmft (nlistToTree nl) = gmnl nl"  
by (auto simp add: gmnl_correct[of nl] nlistToTree_list[of nl]  
                   nlistToTree_inv[of nl]  gmft_correct[of "nlistToTree nl"])

lemma gmftR_gmnl:
  assumes "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
  and "is_leveln_digit n pr \<and> is_measured_digit pr"
  and "\<forall> x \<in> set sf. (is_measured_node x \<and> is_leveln_node n x) \<and> length sf \<le> 4"
  shows "gmft (deepR pr m sf) = gmd pr + gmft m + gmnl sf"
proof-
  from assms have 
    v1: "toList (deepR pr m sf) = digitToList pr @ toList m @ nlistToList sf"
    by (auto simp add: deepR_list)
  from assms  have 
    v2: "is_measured_ftree (deepR pr m sf)"
    by (auto simp add: deepR_inv)
  with v1 have 
    v3: "gmft (deepR pr m sf) = 
        sum_list (map snd (digitToList pr @ toList m @ nlistToList sf))"
    by (auto simp add: gmft_correct)
  have 
    v4:"gmd pr + gmft m + gmnl sf = 
        sum_list (map snd (digitToList pr @ toList m @ nlistToList sf))"
    by (auto simp add: gmd_correct gmft_correct gmnl_correct assms add.assoc)
  with v3 show ?thesis by simp
qed

lemma nsplitTree_invpres: "\<lbrakk>
  is_leveln_ftree n (s:: ('e,'a::monoid_add) FingerTreeStruc);
  is_measured_ftree s;  
  \<not> p i; 
  p (i + (gmft s));
  (nsplitTree p i s) = (l, nd, r)\<rbrakk> 
  \<Longrightarrow> 
  is_leveln_ftree n l
  \<and>
  is_measured_ftree l
  \<and>
  is_leveln_ftree n r
  \<and>
  is_measured_ftree r
  \<and>
  is_leveln_node n nd
  \<and>
  is_measured_node nd
  "
proof (induct p i s arbitrary: n l nd r rule: nsplitTree.induct)
  case 1
  thus ?case by auto
next
  case 2 thus ?case by auto
next
  case (3 p i uu "pr" m sf n l nd r)
  thus ?case
  proof (cases "p (i + gmd pr)")
    case True with 3 show ?thesis
    proof -
      obtain l1 x r1 where 
        l1xr1: "splitDigit p i pr = (l1,x,r1)" 
        by (cases "splitDigit p i pr", blast)
      with True 3 have 
        v1: "l = nlistToTree l1" "nd = x" "r = deepL r1 m sf" by auto
      from l1xr1 have 
        v2: "digitToList pr = nlistToList l1 @ nodeToList x @ nlistToList r1"
        "length l1 \<le> 4" "length r1 \<le> 4"
        by (auto simp add: splitDigit_list)
      from 3(2,3) have 
        pr_m_sf_inv: "is_leveln_digit n pr \<and> is_measured_digit pr"
        "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
        "is_leveln_digit n sf \<and> is_measured_digit sf" by simp_all
      with 3(4,5) pr_m_sf_inv(1) True l1xr1  
        splitDigit_inv'[of p i "pr" l1 x r1 n] have 
        l1_x_r1_inv: 
        "\<forall> x \<in> set l1. (is_measured_node x \<and> is_leveln_node n x)"
        "\<forall> x \<in> set r1. (is_measured_node x \<and> is_leveln_node n x)"
        "is_measured_node x \<and> is_leveln_node n x"
        by auto
      from l1_x_r1_inv v1 v2(3) pr_m_sf_inv have
        ziel3: "is_leveln_ftree n l \<and> is_measured_ftree l \<and>
        is_leveln_ftree n r \<and> is_measured_ftree r \<and> 
        is_leveln_node n nd \<and> is_measured_node nd"
        by (auto simp add: nlistToTree_inv deepL_inv)
      thus ?thesis by simp
    qed
  next
    case False note case1 = this with 3 show ?thesis
    proof (cases "p (i + gmd pr + gmft m)")
      case False with case1 3 show ?thesis
      proof -
        obtain l1 x r1 where 
          l1xr1: "splitDigit p (i + gmd pr + gmft m) sf = (l1,x,r1)" 
          by (cases "splitDigit p (i + gmd pr + gmft m) sf", blast)
        with case1 False 3 have 
          v1: "l = deepR pr m l1" "nd = x" "r = nlistToTree r1" by auto
        from l1xr1 have 
          v2: "digitToList sf = nlistToList l1 @ nodeToList x @ nlistToList r1"
          "length l1 \<le> 4" "length r1 \<le> 4"
          by (auto simp add: splitDigit_list)
        from 3(2,3) have 
          pr_m_sf_inv: "is_leveln_digit n pr \<and> is_measured_digit pr"
          "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
          "is_leveln_digit n sf \<and> is_measured_digit sf" by simp_all
        from 3 have 
          v7: "p (i + gmd pr + gmft m + gmd sf)" by (auto simp add: add.assoc)
        with pr_m_sf_inv 3(4) pr_m_sf_inv(3) case1 False l1xr1  
             splitDigit_inv'[of p "i + gmd pr + gmft m" sf l1 x r1 n] 
        have l1_x_r1_inv: 
          "\<forall> x \<in> set l1. (is_measured_node x \<and> is_leveln_node n x)"
          "\<forall> x \<in> set r1. (is_measured_node x \<and> is_leveln_node n x)"
          "is_measured_node x \<and> is_leveln_node n x"
          by auto
        from l1_x_r1_inv v1 v2(2) pr_m_sf_inv have
          ziel3: "is_leveln_ftree n l \<and> is_measured_ftree l \<and>
          is_leveln_ftree n r \<and> is_measured_ftree r \<and> 
          is_leveln_node n nd \<and> is_measured_node nd"
          by (auto simp add: nlistToTree_inv deepR_inv)
        from ziel3 show ?thesis by simp
      qed
    next
      case True with case1 3 show ?thesis
      proof -
        obtain l1 x r1 where 
          l1_x_r1 :"nsplitTree p (i + gmd pr) m = (l1, x, r1)"
          by (cases "nsplitTree p (i + gmd pr) m", blast)
        from 3(2,3) have 
          pr_m_sf_inv: "is_leveln_digit n pr \<and> is_measured_digit pr"
          "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
          "is_leveln_digit n sf \<and> is_measured_digit sf" by simp_all
        with True case1 
          "3.hyps"[of "i + gmd pr" "i + gmd pr + gmft m" "Suc n" l1 x r1] 
          3(6) l1_x_r1 
        have l1_x_r1_inv: 
          "is_leveln_ftree (Suc n) l1 \<and> is_measured_ftree l1"
          "is_leveln_ftree (Suc n) r1 \<and> is_measured_ftree r1"
          "is_leveln_node (Suc n) x \<and> is_measured_node x"
          by auto
        obtain l2 x2 r2 where l2_x2_r2: 
          "splitDigit p (i + gmd pr + gmft l1) (nodeToDigit x) = (l2,x2,r2)"
          by (cases "splitDigit p (i + gmd pr + gmft l1) (nodeToDigit x)",blast)
        from l1_x_r1_inv have
          ndx_inv: "is_leveln_digit n (nodeToDigit x) \<and>
          is_measured_digit (nodeToDigit x)"
          by (auto simp add: nodeToDigit_inv gmn_gmd)
        note spdi = splitDigit_inv'[of p "i + gmd pr + gmft l1" 
                                      "nodeToDigit x" l2 x2 r2 n]
        from ndx_inv l1_x_r1_inv(1) l2_x2_r2 3(4) have
          l2_x2_r2_inv:
          "\<forall>x\<in>set l2. is_measured_node x \<and> is_leveln_node n x"
          "\<forall>x\<in>set r2. is_measured_node x \<and> is_leveln_node n x"
          "is_measured_node x2 \<and> is_leveln_node n x2"
          by (auto simp add: spdi)
        note spdl =  splitDigit_list[of p "i + gmd pr + gmft l1" 
                                        "nodeToDigit x" l2 x2 r2]
        from l2_x2_r2 have
          l2_x2_r2_list: 
          "digitToList (nodeToDigit x) = 
            nlistToList l2 @ nodeToList x2 @ nlistToList r2"
          "length l2 \<le> 4 \<and> length r2 \<le> 4"
          by (auto simp add: spdl)
        from case1 True 3(6) l1_x_r1 l2_x2_r2 have 
          l_nd_r:
          "l = deepR pr l1 l2"
          "nd = x2"
          "r = deepL r2 r1 sf"
          by auto
        note dr1 = deepR_inv[OF l1_x_r1_inv(1) pr_m_sf_inv(1)]
        from dr1 l2_x2_r2_inv l2_x2_r2_list(2) l_nd_r have 
          l_inv: "is_leveln_ftree n l \<and> is_measured_ftree l"
          by simp
        note dl1 = deepL_inv[OF l1_x_r1_inv(2) pr_m_sf_inv(3)]
        from dl1 l2_x2_r2_inv l2_x2_r2_list(2) l_nd_r have 
          r_inv: "is_leveln_ftree n r \<and> is_measured_ftree r"
          by simp
        from l2_x2_r2_inv l_nd_r have
          nd_inv: "is_leveln_node n nd \<and> is_measured_node nd"
          by simp
        from l_inv r_inv nd_inv
        show ?thesis by simp
      qed
    qed
  qed
qed

lemma nsplitTree_correct: "\<lbrakk>
  is_leveln_ftree n (s:: ('e,'a::monoid_add) FingerTreeStruc);
  is_measured_ftree s;  
  \<And>(a::'a) (b::'a). p a \<Longrightarrow> p (a + b);
  \<not> p i; 
  p (i + (gmft s));
  (nsplitTree p i s) = (l, nd, r)\<rbrakk> 
  \<Longrightarrow> (toList s) = (toList l) @ (nodeToList nd) @ (toList r) 
  \<and>
  \<not> p (i + (gmft l))
  \<and>
  p (i + (gmft l) + (gmn nd))
  \<and>
  is_leveln_ftree n l
  \<and>
  is_measured_ftree l
  \<and>
  is_leveln_ftree n r
  \<and>
  is_measured_ftree r
  \<and>
  is_leveln_node n nd
  \<and>
  is_measured_node nd
  "
proof (induct p i s arbitrary: n l nd r rule: nsplitTree.induct)
  case 1
  thus ?case by auto
next
  case 2 thus ?case by auto
next
  case (3 p i uu "pr" m sf n l nd r)
  thus ?case
  proof (cases "p (i + gmd pr)")
    case True with 3 show ?thesis
    proof -
      obtain l1 x r1 where 
        l1xr1: "splitDigit p i pr = (l1,x,r1)" 
        by (cases "splitDigit p i pr", blast)
      with True 3(7) have 
        v1: "l = nlistToTree l1" "nd = x" "r = deepL r1 m sf" by auto
      from l1xr1 have 
        v2: "digitToList pr = nlistToList l1 @ nodeToList x @ nlistToList r1"
        "length l1 \<le> 4" "length r1 \<le> 4"
        by (auto simp add: splitDigit_list)
      from 3(2,3) have 
        pr_m_sf_inv: "is_leveln_digit n pr \<and> is_measured_digit pr"
        "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
        "is_leveln_digit n sf \<and> is_measured_digit sf" by simp_all
      with 3(4,5) pr_m_sf_inv(1) True l1xr1  
        splitDigit_inv[of p i "pr" n l1 x r1] have 
        l1_x_r1_inv: 
        "\<not> p (i + (gmnl l1))"
        "p (i + (gmnl l1) + (gmn x))"
        "\<forall> x \<in> set l1. (is_measured_node x \<and> is_leveln_node n x)"
        "\<forall> x \<in> set r1. (is_measured_node x \<and> is_leveln_node n x)"
        "is_measured_node x \<and> is_leveln_node n x"
        by auto
      from v2 v1 l1_x_r1_inv(4) pr_m_sf_inv have             
        ziel1: "toList (Deep uu pr m sf) = toList l @ nodeToList nd @ toList r"
        by (auto simp add: nlistToTree_list deepL_list)
      from l1_x_r1_inv(3) v1(1) have 
        v3: "gmft l = gmnl l1" by (simp add: gmnl_gmft)
      with l1_x_r1_inv(1,2) v1 have
        ziel2: " \<not> p (i + gmft l)"
        "p (i + gmft l + gmn nd)"
        by simp_all
      from l1_x_r1_inv(3,4,5) v1 v2(3) pr_m_sf_inv have
        ziel3: "is_leveln_ftree n l \<and> is_measured_ftree l \<and>
        is_leveln_ftree n r \<and> is_measured_ftree r \<and> 
        is_leveln_node n nd \<and> is_measured_node nd"
        by (auto simp add: nlistToTree_inv deepL_inv)
      from ziel1 ziel2 ziel3 show ?thesis by simp
    qed
  next
    case False note case1 = this with 3 show ?thesis
    proof (cases "p (i + gmd pr + gmft m)")
      case False with case1 3 show ?thesis
      proof -
        obtain l1 x r1 where 
          l1xr1: "splitDigit p (i + gmd pr + gmft m) sf = (l1,x,r1)" 
          by (cases "splitDigit p (i + gmd pr + gmft m) sf", blast)
        with case1 False 3(7) have 
          v1: "l = deepR pr m l1" "nd = x" "r = nlistToTree r1" by auto
        from l1xr1 have 
          v2: "digitToList sf = nlistToList l1 @ nodeToList x @ nlistToList r1"
          "length l1 \<le> 4" "length r1 \<le> 4"
          by (auto simp add: splitDigit_list)
        from 3(2,3) have 
          pr_m_sf_inv: "is_leveln_digit n pr \<and> is_measured_digit pr"
          "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
          "is_leveln_digit n sf \<and> is_measured_digit sf" by simp_all
        from 3(3,6) have 
          v7: "p (i + gmd pr + gmft m + gmd sf)" by (auto simp add: add.assoc)
        with pr_m_sf_inv 3(4) pr_m_sf_inv(3) case1 False l1xr1  
             splitDigit_inv[of p "i + gmd pr + gmft m" sf n l1 x r1] 
        have l1_x_r1_inv: 
          "\<not> p (i + gmd pr + gmft m + gmnl l1)"
          "p (i + gmd pr + gmft m + gmnl l1 + gmn x)"
          "\<forall> x \<in> set l1. (is_measured_node x \<and> is_leveln_node n x)"
          "\<forall> x \<in> set r1. (is_measured_node x \<and> is_leveln_node n x)"
          "is_measured_node x \<and> is_leveln_node n x"
          by auto
        from v2 v1 l1_x_r1_inv(3) pr_m_sf_inv have             
          ziel1: "toList (Deep uu pr m sf) = toList l @ nodeToList nd @ toList r"
          by (auto simp add: nlistToTree_list deepR_list)
        from l1_x_r1_inv(4) v1(3) have 
          v3: "gmft r = gmnl r1" by (simp add: gmnl_gmft)
        with l1_x_r1_inv(1,2,3) pr_m_sf_inv v1 v2 have
          ziel2: " \<not> p (i + gmft l)"
          "p (i + gmft l + gmn nd)"
          by (auto simp add: gmftR_gmnl add.assoc)
        from l1_x_r1_inv(3,4,5) v1 v2(2) pr_m_sf_inv have
          ziel3: "is_leveln_ftree n l \<and> is_measured_ftree l \<and>
          is_leveln_ftree n r \<and> is_measured_ftree r \<and> 
          is_leveln_node n nd \<and> is_measured_node nd"
          by (auto simp add: nlistToTree_inv deepR_inv)
        from ziel1 ziel2 ziel3 show ?thesis by simp
      qed
    next
      case True with case1 3 show ?thesis
      proof -
        obtain l1 x r1 where 
          l1_x_r1 :"nsplitTree p (i + gmd pr) m = (l1, x, r1)"
          by (cases "nsplitTree p (i + gmd pr) m") blast
        from 3(2,3) have 
          pr_m_sf_inv: "is_leveln_digit n pr \<and> is_measured_digit pr"
          "is_leveln_ftree (Suc n) m \<and> is_measured_ftree m"
          "is_leveln_digit n sf \<and> is_measured_digit sf" by simp_all
        with True case1 
          "3.hyps"[of "i + gmd pr" "i + gmd pr + gmft m" "Suc n" l1 x r1] 
          3(4) l1_x_r1 
        have l1_x_r1_inv: 
          "\<not> p (i + gmd pr + gmft l1)"
          "p (i + gmd pr + gmft l1 + gmn x)"
          "is_leveln_ftree (Suc n) l1 \<and> is_measured_ftree l1"
          "is_leveln_ftree (Suc n) r1 \<and> is_measured_ftree r1"
          "is_leveln_node (Suc n) x \<and> is_measured_node x"
          and l1_x_r1_list:
          "toList m = toList l1 @ nodeToList x @ toList r1"
          by auto
        obtain l2 x2 r2 where l2_x2_r2: 
          "splitDigit p (i + gmd pr + gmft l1) (nodeToDigit x) = (l2,x2,r2)"
          by (cases "splitDigit p (i + gmd pr + gmft l1) (nodeToDigit x)",blast)
        from l1_x_r1_inv(2,5) have
          ndx_inv: "is_leveln_digit n (nodeToDigit x) \<and>
          is_measured_digit (nodeToDigit x)"
          "p (i + gmd pr + gmft l1 + gmd (nodeToDigit x))"
          by (auto simp add: nodeToDigit_inv gmn_gmd)
        note spdi = splitDigit_inv[of p "i + gmd pr + gmft l1" 
                                      "nodeToDigit x" n l2 x2 r2]
        from ndx_inv l1_x_r1_inv(1) l2_x2_r2 3(4) have
          l2_x2_r2_inv:"\<not> p (i + gmd pr + gmft l1 + gmnl l2)"
          "p (i + gmd pr + gmft l1 + gmnl l2 + gmn x2)"
          "\<forall>x\<in>set l2. is_measured_node x \<and> is_leveln_node n x"
          "\<forall>x\<in>set r2. is_measured_node x \<and> is_leveln_node n x"
          "is_measured_node x2 \<and> is_leveln_node n x2"
          by (auto simp add: spdi)
        note spdl =  splitDigit_list[of p "i + gmd pr + gmft l1" 
                                        "nodeToDigit x" l2 x2 r2]
        from l2_x2_r2 have
          l2_x2_r2_list: 
          "digitToList (nodeToDigit x) = 
            nlistToList l2 @ nodeToList x2 @ nlistToList r2"
          "length l2 \<le> 4 \<and> length r2 \<le> 4"
          by (auto simp add: spdl)
        from case1 True 3(7) l1_x_r1 l2_x2_r2 have 
          l_nd_r:
          "l = deepR pr l1 l2"
          "nd = x2"
          "r = deepL r2 r1 sf"
          by auto
        note dr1 = deepR_inv[OF l1_x_r1_inv(3) pr_m_sf_inv(1)]
        from dr1 l2_x2_r2_inv(3) l2_x2_r2_list(2) l_nd_r have 
          l_inv: "is_leveln_ftree n l \<and> is_measured_ftree l"
          by simp
        note dl1 = deepL_inv[OF l1_x_r1_inv(4) pr_m_sf_inv(3)]
        from dl1 l2_x2_r2_inv(4) l2_x2_r2_list(2) l_nd_r have 
          r_inv: "is_leveln_ftree n r \<and> is_measured_ftree r"
          by simp
        from l2_x2_r2_inv l_nd_r have
          nd_inv: "is_leveln_node n nd \<and> is_measured_node nd"
          by simp
        from l_nd_r(1,2) l2_x2_r2_inv(1,2,3) 
             l1_x_r1_inv(3) l2_x2_r2_list(2) pr_m_sf_inv(1)
        have split_point:
          " \<not> p (i + gmft l)"
          "p (i + gmft l + gmn nd)"
          by (auto simp add: gmftR_gmnl add.assoc)
        from l2_x2_r2_list have x_list: 
          "nodeToList x = nlistToList l2 @ nodeToList x2 @ nlistToList r2"
          by (simp add: nodeToDigit_list)
        from l1_x_r1_inv(3) pr_m_sf_inv(1) 
             l2_x2_r2_inv(3) l2_x2_r2_list(2) l_nd_r(1)
        have l_list: "toList l = digitToList pr @ toList l1 @ nlistToList l2"
          by (auto simp add: deepR_list)
        from l1_x_r1_inv(4) pr_m_sf_inv(3) l2_x2_r2_inv(4) 
             l2_x2_r2_list(2) l_nd_r(3)
        have r_list: "toList r = nlistToList r2 @ toList r1 @ digitToList sf"
          by (auto simp add: deepL_list)
        from x_list l1_x_r1_list l_list r_list l_nd_r
        have  "toList (Deep uu pr m sf) = toList l @ nodeToList nd @ toList r"
          by auto
        with split_point l_inv r_inv nd_inv
        show ?thesis by simp
      qed
    qed
  qed
qed

text \<open>
  A predicate on the elements of a monoid is called {\em monotone},
  iff, when it holds for some value $a$, it also holds for all values $a+b$:
\<close>

text \<open>Split a finger tree by a monotone predicate on the annotations, using
    a given initial value. Intuitively, the elements are summed up from left to 
    right, and the split is done when the predicate first holds for the sum.
    The predicate must not hold for the initial value of the summation, and must
    hold for the sum of all elements.
\<close>
definition splitTree 
  :: "('a::monoid_add \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> ('e, 'a) FingerTreeStruc 
    \<Rightarrow> ('e, 'a) FingerTreeStruc \<times> ('e \<times> 'a) \<times> ('e, 'a) FingerTreeStruc" 
  where
  "splitTree p i t = (let (l, x, r) = nsplitTree p i t in (l, (n_unwrap x), r))"

lemma splitTree_invpres: 
  assumes inv: "ft_invar (s:: ('e,'a::monoid_add) FingerTreeStruc)"
  assumes init_ff: "\<not> p i"
  assumes sum_tt: "p (i + annot s)"
  assumes fmt: "(splitTree p i s) = (l, (e,a), r)"
  shows "ft_invar l" and "ft_invar r"
proof -
  obtain l1 nd r1 where 
    l1_nd_r1: "nsplitTree p i s = (l1, nd, r1)"
    by (cases "nsplitTree p i s", blast)
  
  with assms have 
    l0: "l = l1"
    "(e,a) = n_unwrap nd"
    "r = r1"
    by (auto simp add: splitTree_def)
  note nsp = nsplitTree_invpres[of 0 s p i l1 nd r1]

  from assms have "p (i + gmft s)" by (simp add:  ft_invar_def annot_def)
  with assms l1_nd_r1 l0 have 
    v1:
    "is_leveln_ftree 0 l \<and> is_measured_ftree l"
    "is_leveln_ftree 0 r \<and> is_measured_ftree r"
    "is_leveln_node 0 nd  \<and> is_measured_node nd"
    by (auto simp add: nsp ft_invar_def)
  thus "ft_invar l" and "ft_invar r"
    by (simp_all add: ft_invar_def annot_def)
qed


lemma splitTree_correct: 
  assumes inv: "ft_invar (s:: ('e,'a::monoid_add) FingerTreeStruc)"
  assumes mono: "\<forall>a b. p a \<longrightarrow> p (a + b)"
  assumes init_ff: "\<not> p i"
  assumes sum_tt: "p (i + annot s)"
  assumes fmt: "(splitTree p i s) = (l, (e,a), r)"
  shows "(toList s) = (toList l) @ (e,a) # (toList r)"
  and   "\<not> p (i + annot l)"
  and   "p (i + annot l + a)"
  and   "ft_invar l" and "ft_invar r"
proof -
  obtain l1 nd r1 where 
    l1_nd_r1: "nsplitTree p i s = (l1, nd, r1)"
    by (cases "nsplitTree p i s", blast)
  
  with assms have 
    l0: "l = l1"
    "(e,a) = n_unwrap nd"
    "r = r1"
    by (auto simp add: splitTree_def)
  note nsp = nsplitTree_correct[of 0 s p i l1 nd r1]

  from assms have "p (i + gmft s)" by (simp add:  ft_invar_def annot_def)
  with assms l1_nd_r1 l0 have 
    v1:
    "(toList s) = (toList l) @ (nodeToList nd) @ (toList r)" 
    "\<not> p (i + (gmft l))"
    "p (i + (gmft l) + (gmn nd))"
    "is_leveln_ftree 0 l \<and> is_measured_ftree l"
    "is_leveln_ftree 0 r \<and> is_measured_ftree r"
    "is_leveln_node 0 nd  \<and> is_measured_node nd"
    by (auto simp add: nsp ft_invar_def)
  from v1(6) l0(2) have 
    ndea: "nd = Tip e a"
    by (cases nd)  auto
  hence nd_list_inv: "nodeToList nd = [(e,a)]"
    "gmn nd = a" by simp_all  
  with v1 show  "(toList s) = (toList l) @ (e,a) # (toList r)"
    and   "\<not> p (i + annot l)"
    and   "p (i + annot l + a)"
    and   "ft_invar l" and "ft_invar r"
    by (simp_all add: ft_invar_def annot_def)
qed

lemma splitTree_correctE: 
  assumes inv: "ft_invar (s:: ('e,'a::monoid_add) FingerTreeStruc)"
  assumes mono: "\<forall>a b. p a \<longrightarrow> p (a + b)"
  assumes init_ff: "\<not> p i"
  assumes sum_tt: "p (i + annot s)"
  obtains l e a r where
    "(splitTree p i s) = (l, (e,a), r)" and
    "(toList s) = (toList l) @ (e,a) # (toList r)" and
    "\<not> p (i + annot l)" and
    "p (i + annot l + a)" and
    "ft_invar l" and "ft_invar r"
proof -
  obtain l e a r where fmt: "(splitTree p i s) = (l, (e,a), r)" 
    by (cases "(splitTree p i s)") auto
  from splitTree_correct[of s p, OF assms fmt] fmt
  show ?thesis
    by (blast intro: that)
qed


subsubsection \<open>Folding\<close>

fun foldl_node :: "('s \<Rightarrow> 'e \<times> 'a \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> ('e,'a) Node \<Rightarrow> 's" where
  "foldl_node f \<sigma> (Tip e a) = f \<sigma> (e,a)"|
  "foldl_node f \<sigma> (Node2 _ a b) = foldl_node f (foldl_node f \<sigma> a) b"|
  "foldl_node f \<sigma> (Node3 _ a b c) = 
    foldl_node f (foldl_node f (foldl_node f \<sigma> a) b) c"

primrec foldl_digit :: "('s \<Rightarrow> 'e \<times> 'a \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> ('e,'a) Digit \<Rightarrow> 's" where
  "foldl_digit f \<sigma> (One n1) = foldl_node f \<sigma> n1"|
  "foldl_digit f \<sigma> (Two n1 n2) = foldl_node f (foldl_node f \<sigma> n1) n2"|
  "foldl_digit f \<sigma> (Three n1 n2 n3) = 
    foldl_node f (foldl_node f (foldl_node f \<sigma> n1) n2) n3"|
  "foldl_digit f \<sigma> (Four n1 n2 n3 n4) = 
    foldl_node f (foldl_node f (foldl_node f (foldl_node f \<sigma> n1) n2) n3) n4"


primrec foldr_node :: "('e \<times> 'a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('e,'a) Node \<Rightarrow> 's  \<Rightarrow> 's" where
  "foldr_node f (Tip e a) \<sigma> = f (e,a) \<sigma> "|
  "foldr_node f (Node2 _ a b) \<sigma> = foldr_node f a (foldr_node f b \<sigma>)"|
  "foldr_node f (Node3 _ a b c) \<sigma> 
    = foldr_node f a (foldr_node f b (foldr_node f c \<sigma>))"

primrec foldr_digit :: "('e \<times> 'a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('e,'a) Digit \<Rightarrow> 's \<Rightarrow> 's" where
  "foldr_digit f (One n1) \<sigma> = foldr_node f n1 \<sigma>"|
  "foldr_digit f (Two n1 n2) \<sigma> = foldr_node f n1 (foldr_node f n2 \<sigma>)"|
  "foldr_digit f (Three n1 n2 n3) \<sigma> =
    foldr_node f n1 (foldr_node f n2 (foldr_node f n3 \<sigma>))"|
  "foldr_digit f (Four n1 n2 n3 n4) \<sigma> =
    foldr_node f n1 (foldr_node f n2 (foldr_node f n3 (foldr_node f n4 \<sigma>)))"

lemma foldl_node_correct: 
  "foldl_node f \<sigma> nd = List.foldl f \<sigma> (nodeToList nd)"
  by (induct nd arbitrary: "\<sigma>") (auto simp add: nodeToList_def)

lemma foldl_digit_correct:
  "foldl_digit f \<sigma> d = List.foldl f \<sigma> (digitToList d)"
  by (induct d arbitrary: "\<sigma>") (auto 
    simp add: digitToList_def foldl_node_correct)
  
lemma foldr_node_correct: 
  "foldr_node f nd \<sigma> = List.foldr f (nodeToList nd) \<sigma>"
by (induct nd arbitrary: "\<sigma>") (auto simp add: nodeToList_def)

lemma foldr_digit_correct:
  "foldr_digit f d \<sigma> = List.foldr f (digitToList d) \<sigma>"
  by (induct d arbitrary: "\<sigma>") (auto 
    simp add: digitToList_def foldr_node_correct)

text "Fold from left"
primrec foldl :: "('s \<Rightarrow> 'e \<times> 'a \<Rightarrow> 's) \<Rightarrow> 's \<Rightarrow> ('e,'a) FingerTreeStruc \<Rightarrow> 's"
  where
  "foldl f \<sigma> Empty = \<sigma>"|
  "foldl f \<sigma> (Single nd) = foldl_node f \<sigma> nd"|
  "foldl f \<sigma> (Deep _ d1 m d2) = 
    foldl_digit f (foldl f (foldl_digit f \<sigma> d1) m) d2"

lemma foldl_correct:
  "foldl f \<sigma> t = List.foldl f \<sigma> (toList t)"
  by (induct t arbitrary: "\<sigma>") (auto 
    simp add: toList_def foldl_node_correct foldl_digit_correct)

text "Fold from right"
primrec foldr :: "('e \<times> 'a \<Rightarrow> 's \<Rightarrow> 's) \<Rightarrow> ('e,'a) FingerTreeStruc \<Rightarrow> 's \<Rightarrow> 's"
  where
  "foldr f Empty \<sigma> = \<sigma>"|
  "foldr f (Single nd) \<sigma> = foldr_node f nd \<sigma>"|
  "foldr f (Deep _ d1 m d2) \<sigma> 
    = foldr_digit f d1 (foldr f m(foldr_digit f d2 \<sigma>))"

lemma foldr_correct:
  "foldr f t \<sigma> = List.foldr f (toList t) \<sigma>"
  by (induct t arbitrary: "\<sigma>") (auto 
    simp add: toList_def foldr_node_correct foldr_digit_correct)

subsubsection "Number of elements"

primrec count_node :: "('e, 'a) Node \<Rightarrow> nat" where
  "count_node (Tip _ a) = 1" |
  "count_node (Node2 _ a b) = count_node a + count_node b" |
  "count_node (Node3 _ a b c) = count_node a + count_node b + count_node c"

primrec count_digit :: "('e,'a) Digit \<Rightarrow> nat" where
  "count_digit (One a) = count_node a" |
  "count_digit (Two a b) = count_node a + count_node b" |
  "count_digit (Three a b c) = count_node a + count_node b + count_node c" |
  "count_digit (Four a b c d) 
    = count_node a + count_node b + count_node c + count_node d"

lemma count_node_correct:
  "count_node n = length (nodeToList n)"
  by (induct n,auto simp add: nodeToList_def count_node_def)

lemma count_digit_correct:
  "count_digit d = length (digitToList d)"
  by (cases d, auto simp add: digitToList_def count_digit_def count_node_correct)

primrec count :: "('e,'a) FingerTreeStruc \<Rightarrow> nat" where 
  "count Empty = 0" |
  "count (Single a) = count_node a" |
  "count (Deep _ pr m sf) = count_digit pr + count m + count_digit sf"

lemma count_correct[simp]:
  "count t = length (toList t)"
  by (induct t, 
    auto simp add: toList_def count_def 
                   count_digit_correct count_node_correct)
end

(* Expose finger tree functions as qualified names.
  Generate code equations *)
interpretation FingerTreeStruc: FingerTreeStruc_loc .

(* Hide the concrete syntax *)
no_notation FingerTreeStruc.lcons (infixr "\<lhd>" 65)
no_notation FingerTreeStruc.rcons (infixl "\<rhd>" 65)

subsection "Hiding the invariant"
text_raw\<open>\label{sec:hide_invar}\<close>
text \<open>
  In this section, we define the datatype of all FingerTrees that fulfill their
  invariant, and define the operations to work on this datatype.
  The advantage is, that the correctness lemmas do no longer contain 
  explicit invariant predicates, what makes them more handy to use.
\<close>

subsubsection "Datatype"
typedef (overloaded) ('e, 'a) FingerTree = 
  "{t :: ('e, 'a::monoid_add) FingerTreeStruc. FingerTreeStruc.ft_invar t}"
proof -
  have "Empty \<in> ?FingerTree" by (simp)
  then show ?thesis ..
qed

lemma Rep_FingerTree_invar[simp]: "FingerTreeStruc.ft_invar (Rep_FingerTree t)"
  using Rep_FingerTree by simp

lemma [simp]: 
  "FingerTreeStruc.ft_invar t \<Longrightarrow> Rep_FingerTree (Abs_FingerTree t) = t"
  using Abs_FingerTree_inverse by simp

lemma [simp, code abstype]: "Abs_FingerTree (Rep_FingerTree t) = t"
  by (rule Rep_FingerTree_inverse)

typedef (overloaded) ('e,'a) viewres =
  "{ r:: (('e \<times> 'a) \<times> ('e,'a::monoid_add) FingerTreeStruc) option . 
    case r of None \<Rightarrow> True | Some (a,t) \<Rightarrow> FingerTreeStruc.ft_invar t}"
  apply (rule_tac x=None in exI)
  apply auto
  done

lemma [simp, code abstype]: "Abs_viewres (Rep_viewres x) = x" 
  by (rule Rep_viewres_inverse)

lemma Abs_viewres_inverse_None[simp]: 
  "Rep_viewres (Abs_viewres None) = None" 
  by (simp add: Abs_viewres_inverse)

lemma Abs_viewres_inverse_Some: 
  "FingerTreeStruc.ft_invar t \<Longrightarrow> 
    Rep_viewres (Abs_viewres (Some (a,t))) = Some (a,t)"
  by (auto simp add: Abs_viewres_inverse)

definition [code]: "extract_viewres_isNone r == Rep_viewres r = None"
definition [code]: "extract_viewres_a r == 
    case (Rep_viewres r) of Some (a,t) \<Rightarrow> a"
definition "extract_viewres_t r == 
  case (Rep_viewres r) of None \<Rightarrow> Abs_FingerTree Empty 
                        | Some (a,t) \<Rightarrow> Abs_FingerTree t"
lemma [code abstract]: "Rep_FingerTree (extract_viewres_t r) = 
    (case (Rep_viewres r) of None \<Rightarrow> Empty | Some (a,t) \<Rightarrow> t)"
  apply (cases r)
  apply (auto split: option.split option.split_asm 
             simp add: extract_viewres_t_def Abs_viewres_inverse_Some)
  done

definition "extract_viewres r == 
    if extract_viewres_isNone r then None 
    else Some (extract_viewres_a r, extract_viewres_t r)"

typedef (overloaded) ('e,'a) splitres =
  "{ ((l,a,r):: (('e,'a) FingerTreeStruc \<times> ('e \<times> 'a) \<times> ('e,'a::monoid_add) FingerTreeStruc))
    | l a r.
        FingerTreeStruc.ft_invar l \<and> FingerTreeStruc.ft_invar r}"
  apply (rule_tac x="(Empty,undefined,Empty)" in exI)
  apply auto
  done

lemma [simp, code abstype]: "Abs_splitres (Rep_splitres x) = x" 
  by (rule Rep_splitres_inverse)

lemma Abs_splitres_inverse: 
  "FingerTreeStruc.ft_invar r \<Longrightarrow> FingerTreeStruc.ft_invar s \<Longrightarrow> 
      Rep_splitres (Abs_splitres ((r,a,s))) = (r,a,s)"
  by (auto simp add: Abs_splitres_inverse)

definition [code]: "extract_splitres_a r == case (Rep_splitres r) of (l,a,s) \<Rightarrow> a"
definition "extract_splitres_l r == case (Rep_splitres r) of (l,a,r) \<Rightarrow> 
    Abs_FingerTree l"
lemma [code abstract]: "Rep_FingerTree (extract_splitres_l r) = (case 
    (Rep_splitres r) of (l,a,r) \<Rightarrow> l)"
  apply (cases r)
  apply (auto split: option.split option.split_asm 
    simp add: extract_splitres_l_def Abs_splitres_inverse)
  done
definition "extract_splitres_r r == case (Rep_splitres r) of (l,a,r) \<Rightarrow> 
    Abs_FingerTree r"
lemma [code abstract]: "Rep_FingerTree (extract_splitres_r r) = (case 
  (Rep_splitres r) of (l,a,r) \<Rightarrow> r)"
  apply (cases r)
  apply (auto split: option.split option.split_asm 
    simp add: extract_splitres_r_def Abs_splitres_inverse)
  done

definition "extract_splitres r == 
  (extract_splitres_l r,
  extract_splitres_a r,
  extract_splitres_r r)"

subsubsection "Definition of Operations"
locale FingerTree_loc
begin
  definition [code]: "toList t == FingerTreeStruc.toList (Rep_FingerTree t)"
  definition empty where "empty == Abs_FingerTree FingerTreeStruc.Empty"
  lemma [code abstract]: "Rep_FingerTree empty = FingerTreeStruc.Empty"
    by (simp add: empty_def)

  lemma empty_rep: "t=empty \<longleftrightarrow> Rep_FingerTree t = Empty"
    apply (auto simp add: empty_def)
    apply (metis Rep_FingerTree_inverse)
    done


  definition [code]: "annot t == FingerTreeStruc.annot (Rep_FingerTree t)"
  definition "toTree t == Abs_FingerTree (FingerTreeStruc.toTree t)"
  lemma [code abstract]: "Rep_FingerTree (toTree t) = FingerTreeStruc.toTree t"
    by (simp add: toTree_def)
  definition "lcons a t == 
    Abs_FingerTree (FingerTreeStruc.lcons a (Rep_FingerTree t))"
  lemma [code abstract]: 
    "Rep_FingerTree (lcons a t) = (FingerTreeStruc.lcons a (Rep_FingerTree t))"
    by (simp add: lcons_def FingerTreeStruc.lcons_correct)
  definition "rcons t a == 
    Abs_FingerTree (FingerTreeStruc.rcons (Rep_FingerTree t) a)"
  lemma [code abstract]: 
    "Rep_FingerTree (rcons t a) = (FingerTreeStruc.rcons (Rep_FingerTree t) a)"
    by (simp add: rcons_def FingerTreeStruc.rcons_correct)

  definition "viewL_aux t == 
    Abs_viewres (FingerTreeStruc.viewL (Rep_FingerTree t))"
  definition "viewL t == extract_viewres (viewL_aux t)"
  lemma [code abstract]:
    "Rep_viewres (viewL_aux t) = (FingerTreeStruc.viewL (Rep_FingerTree t))"
    apply (cases "(FingerTreeStruc.viewL (Rep_FingerTree t))")
    apply (auto simp add: viewL_aux_def )
    apply (cases "Rep_FingerTree t = Empty")
    apply simp
    apply (auto 
      elim!: FingerTreeStruc.viewL_correct_nonEmpty
                 [of "Rep_FingerTree t", simplified]
      simp add: Abs_viewres_inverse_Some)
    done

  definition "viewR_aux t == 
    Abs_viewres (FingerTreeStruc.viewR (Rep_FingerTree t))"
  definition "viewR t == extract_viewres (viewR_aux t)"
  lemma [code abstract]:
    "Rep_viewres (viewR_aux t) = (FingerTreeStruc.viewR (Rep_FingerTree t))"
    apply (cases "(FingerTreeStruc.viewR (Rep_FingerTree t))")
    apply (auto simp add: viewR_aux_def )
    apply (cases "Rep_FingerTree t = Empty")
    apply simp
    apply (auto 
      elim!: FingerTreeStruc.viewR_correct_nonEmpty
                [of "Rep_FingerTree t", simplified]
      simp add: Abs_viewres_inverse_Some)
    done
  
  definition [code]: "isEmpty t == FingerTreeStruc.isEmpty (Rep_FingerTree t)"
  definition [code]: "head t = FingerTreeStruc.head (Rep_FingerTree t)"
  definition "tail t \<equiv> 
    if t=empty then 
      empty 
    else 
      Abs_FingerTree (FingerTreeStruc.tail (Rep_FingerTree t))"
    \<comment> \<open>Make function total, to allow abstraction\<close>
  lemma [code abstract]: "Rep_FingerTree (tail t) = 
    (if (FingerTreeStruc.isEmpty (Rep_FingerTree t)) then Empty 
     else FingerTreeStruc.tail (Rep_FingerTree t))"
    apply (simp add: tail_def FingerTreeStruc.tail_correct FingerTreeStruc.isEmpty_def empty_rep)
    apply (auto simp add: empty_def)
    done

  definition [code]: "headR t = FingerTreeStruc.headR (Rep_FingerTree t)"
  definition "tailR t \<equiv> 
    if t=empty then 
      empty 
    else 
      Abs_FingerTree (FingerTreeStruc.tailR (Rep_FingerTree t))"
  lemma [code abstract]: "Rep_FingerTree (tailR t) = 
    (if (FingerTreeStruc.isEmpty (Rep_FingerTree t)) then Empty 
    else FingerTreeStruc.tailR (Rep_FingerTree t))"
    apply (simp add: tailR_def FingerTreeStruc.tailR_correct FingerTreeStruc.isEmpty_def empty_rep)
    apply (simp add: empty_def)
    done

  definition "app s t = Abs_FingerTree (
    FingerTreeStruc.app (Rep_FingerTree s) (Rep_FingerTree t))"
  lemma [code abstract]:
    "Rep_FingerTree (app s t) = 
      FingerTreeStruc.app (Rep_FingerTree s) (Rep_FingerTree t)"
    by (simp add: app_def FingerTreeStruc.app_correct)

  definition "splitTree_aux p i t == if (\<not>p i \<and> p (i+annot t)) then
    Abs_splitres (FingerTreeStruc.splitTree p i (Rep_FingerTree t))
  else
    Abs_splitres (Empty,undefined,Empty)"
  definition "splitTree p i t == extract_splitres (splitTree_aux p i t)"

  lemma [code abstract]:
    "Rep_splitres (splitTree_aux p i t) = (if (\<not>p i \<and> p (i+annot t)) then
      (FingerTreeStruc.splitTree p i (Rep_FingerTree t))
    else
      (Empty,undefined,Empty))"
    using FingerTreeStruc.splitTree_invpres[of "Rep_FingerTree t" p i]
    apply (auto simp add: splitTree_aux_def annot_def Abs_splitres_inverse)
    apply (cases "FingerTreeStruc.splitTree p i (Rep_FingerTree t)")
    apply (force simp add: Abs_FingerTree_inverse Abs_splitres_inverse)
    done
    
  definition foldl where 
    [code]: "foldl f \<sigma> t == FingerTreeStruc.foldl f \<sigma> (Rep_FingerTree t)"
  definition foldr where 
    [code]: "foldr f t \<sigma> == FingerTreeStruc.foldr f (Rep_FingerTree t) \<sigma>"
  definition count where 
    [code]: "count t == FingerTreeStruc.count (Rep_FingerTree t)"


subsubsection "Correctness statements"
  lemma empty_correct: "toList t = [] \<longleftrightarrow> t=empty"
    apply (unfold toList_def empty_rep)
    apply (simp add: FingerTreeStruc.toList_empty)
    done

  lemma toList_of_empty[simp]: "toList empty = []"
    apply (unfold toList_def empty_def)
    apply (auto simp add: FingerTreeStruc.toList_empty)
    done

  lemma annot_correct: "annot t = sum_list (map snd (toList t))"
    apply (unfold toList_def annot_def)
    apply (simp add: FingerTreeStruc.annot_correct)
    done

  lemma toTree_correct: "toList (toTree l) = l"
    apply (unfold toList_def toTree_def)
    apply (simp add: FingerTreeStruc.toTree_correct)
    done

  lemma lcons_correct: "toList (lcons a t) = a#toList t"
    apply (unfold toList_def lcons_def)
    apply (simp add: FingerTreeStruc.lcons_correct)
    done

  lemma rcons_correct: "toList (rcons t a) = toList t@[a]"
    apply (unfold toList_def rcons_def)
    apply (simp add: FingerTreeStruc.rcons_correct)
    done

  lemma viewL_correct: 
    "t = empty \<Longrightarrow> viewL t = None"
    "t \<noteq> empty \<Longrightarrow> \<exists>a s. viewL t = Some (a,s) \<and> toList t = a#toList s"
    apply (unfold toList_def viewL_def viewL_aux_def 
      extract_viewres_def extract_viewres_isNone_def 
      extract_viewres_a_def
      extract_viewres_t_def
      empty_rep)
    apply (simp add: FingerTreeStruc.viewL_correct)
    apply (drule FingerTreeStruc.viewL_correct(2)[OF Rep_FingerTree_invar])
    apply (auto simp add: Abs_viewres_inverse)
    done

  lemma viewL_empty[simp]: "viewL empty = None"
    using viewL_correct by auto

  lemma viewL_nonEmpty: 
    assumes "t\<noteq>empty"
    obtains a s where "viewL t = Some (a,s)" "toList t = a#toList s"
    using assms viewL_correct by blast

  lemma viewR_correct: 
    "t = empty \<Longrightarrow> viewR t = None"
    "t \<noteq> empty \<Longrightarrow> \<exists>a s. viewR t = Some (a,s) \<and> toList t = toList s@[a]"
    apply (unfold toList_def viewR_def viewR_aux_def 
      extract_viewres_def extract_viewres_isNone_def 
      extract_viewres_a_def
      extract_viewres_t_def
      empty_rep)
    apply (simp add: FingerTreeStruc.viewR_correct)
    apply (drule FingerTreeStruc.viewR_correct(2)[OF Rep_FingerTree_invar])
    apply (auto simp add: Abs_viewres_inverse)
    done

  lemma viewR_empty[simp]: "viewR empty = None"
    using viewR_correct by auto

  lemma viewR_nonEmpty: 
    assumes "t\<noteq>empty"
    obtains a s where "viewR t = Some (a,s)" "toList t = toList s@[a]"
    using assms viewR_correct by blast

  lemma isEmpty_correct: "isEmpty t \<longleftrightarrow> t=empty"
    apply (unfold toList_def isEmpty_def empty_rep)
    apply (simp add: FingerTreeStruc.isEmpty_correct FingerTreeStruc.toList_empty)
    done

  lemma head_correct: "t\<noteq>empty \<Longrightarrow> head t = hd (toList t)"
    apply (unfold toList_def head_def empty_rep)
    apply (simp add: FingerTreeStruc.head_correct)
    done

  lemma tail_correct: "t\<noteq>empty \<Longrightarrow> toList (tail t) = tl (toList t)"
    apply (unfold toList_def tail_def empty_rep)
    apply (simp add: FingerTreeStruc.tail_correct)
    done

  lemma headR_correct: "t\<noteq>empty \<Longrightarrow> headR t = last (toList t)"
    apply (unfold toList_def headR_def empty_rep)
    apply (simp add: FingerTreeStruc.headR_correct)
    done

  lemma tailR_correct: "t\<noteq>empty \<Longrightarrow> toList (tailR t) = butlast (toList t)"
    apply (unfold toList_def tailR_def empty_rep)
    apply (simp add: FingerTreeStruc.tailR_correct)
    done
    
  lemma app_correct: "toList (app s t) = toList s @ toList t"
    apply (unfold toList_def app_def)
    apply (simp add: FingerTreeStruc.app_correct)
    done

  lemma splitTree_correct:
    assumes mono: "\<forall>a b. p a \<longrightarrow> p (a + b)"
    assumes init_ff: "\<not> p i"
    assumes sum_tt: "p (i + annot s)"
    assumes fmt: "(splitTree p i s) = (l, (e,a), r)"
    shows "(toList s) = (toList l) @ (e,a) # (toList r)"
    and   "\<not> p (i + annot l)"
    and   "p (i + annot l + a)"
    apply (rule
      FingerTreeStruc.splitTree_correctE[
      where p=p and s="Rep_FingerTree s",
      OF _ mono init_ff sum_tt[unfolded annot_def],
      simplified
      ])
    using fmt
    apply (unfold toList_def splitTree_aux_def splitTree_def annot_def 
      extract_splitres_def extract_splitres_l_def 
      extract_splitres_a_def extract_splitres_r_def) [1]
    apply (auto split: if_split_asm prod.split_asm 
      simp add: init_ff sum_tt[unfolded annot_def] Abs_splitres_inverse) [1]

    apply (rule
      FingerTreeStruc.splitTree_correctE[
      where p=p and s="Rep_FingerTree s",
      OF _ mono init_ff sum_tt[unfolded annot_def],
      simplified
      ])
    using fmt
    apply (unfold toList_def splitTree_aux_def splitTree_def annot_def 
      extract_splitres_def extract_splitres_l_def 
      extract_splitres_a_def extract_splitres_r_def) [1]
    apply (auto split: if_split_asm prod.split_asm 
      simp add: init_ff sum_tt[unfolded annot_def] Abs_splitres_inverse) [1]

    apply (rule
      FingerTreeStruc.splitTree_correctE[
      where p=p and s="Rep_FingerTree s",
      OF _ mono init_ff sum_tt[unfolded annot_def],
      simplified
      ])
    using fmt
    apply (unfold toList_def splitTree_aux_def splitTree_def annot_def 
      extract_splitres_def extract_splitres_l_def 
      extract_splitres_a_def extract_splitres_r_def) [1]
    apply (auto split: if_split_asm prod.split_asm 
      simp add: init_ff sum_tt[unfolded annot_def] Abs_splitres_inverse) [1]
    done

  lemma splitTree_correctE:
    assumes mono: "\<forall>a b. p a \<longrightarrow> p (a + b)"
    assumes init_ff: "\<not> p i"
    assumes sum_tt: "p (i + annot s)"
    obtains l e a r where
    "(splitTree p i s) = (l, (e,a), r)" and
    "(toList s) = (toList l) @ (e,a) # (toList r)" and
    "\<not> p (i + annot l)" and
    "p (i + annot l + a)"
  proof -
    obtain l e a r where fmt: "(splitTree p i s) = (l, (e,a), r)" 
      by (cases "(splitTree p i s)") auto
    from splitTree_correct[of p, OF assms fmt] fmt
    show ?thesis
      by (blast intro: that)
  qed

  lemma foldl_correct: "foldl f \<sigma> t = List.foldl f \<sigma> (toList t)"
    apply (unfold toList_def foldl_def)
    apply (simp add: FingerTreeStruc.foldl_correct)
    done

  lemma foldr_correct: "foldr f t \<sigma> = List.foldr f (toList t) \<sigma>"
    apply (unfold toList_def foldr_def)
    apply (simp add: FingerTreeStruc.foldr_correct)
    done

  lemma count_correct: "count t = length (toList t)"
    apply (unfold toList_def count_def)
    apply (simp add: FingerTreeStruc.count_correct)
    done


end

interpretation FingerTree: FingerTree_loc .

text_raw\<open>\clearpage\<close>
subsection "Interface Documentation"
text_raw\<open>\label{sec:doc}\<close>

  text \<open>
    In this section, we list all supported operations on finger trees,
    along with a short plaintext documentation and their correctness statements.
\<close>

(*#DOC
  fun [no_spec] FingerTree.toList
    Convert to list ($O(n)$)

  fun FingerTree.empty
    The empty finger tree ($O(1)$)

  fun FingerTree.annot
    Return sum of all annotations ($O(1)$)

  fun FingerTree.toTree
    Convert list to finger tree ($O(n\log(n))$)

  fun FingerTree.lcons
    Append element at the left end ($O(\log(n))$, $O(1)$ amortized)

  fun FingerTree.rcons
    Append element at the right end ($O(\log(n))$, $O(1)$ amortized)

  fun FingerTree.viewL
    Detach leftmost element ($O(\log(n))$, $O(1)$ amortized)

  fun FingerTree.viewR
    Detach rightmost element ($O(\log(n))$, $O(1)$ amortized)

  fun FingerTree.isEmpty
    Check whether tree is empty ($O(1)$)

  fun FingerTree.head
    Get leftmost element of non-empty tree ($O(\log(n))$)

  fun FingerTree.tail
    Get all but leftmost element of non-empty tree ($O(\log(n))$)

  fun FingerTree.headR
    Get rightmost element of non-empty tree ($O(\log(n))$)

  fun FingerTree.tailR
    Get all but rightmost element of non-empty tree ($O(\log(n))$)

  fun FingerTree.app
    Concatenate two finger trees ($O(\log(m+n))$)

  fun [long_type] FingerTree.splitTree
    Split tree by a monotone predicate. ($O(\log(n))$)

    A predicate $p$ over the annotations is called monotone, iff, for all 
    annotations
    $a,b$ with $p(a)$, we have already $p(a+b)$.

    Splitting is done by specifying a monotone predicate $p$ that does not hold
    for the initial value $i$ of the summation, but holds for $i$ plus the sum
    of all annotations. The tree is then split at the position where $p$ starts to
    hold for the sum of all elements up to that position.

  fun [long_type] FingerTree.foldl
    Fold with function from left

  fun [long_type] FingerTree.foldr
    Fold with function from right

  fun FingerTree.count
    Return the number of elements

*)

text \<open>
    \underline{@{term_type "FingerTree.toList"}}\\                                               
        Convert to list ($O(n)$)\\                                                               


    \underline{@{term_type "FingerTree.empty"}}\\
        The empty finger tree ($O(1)$)\\         
    {\bf Spec} \<open>FingerTree.empty_correct\<close>:
    @{thm [display] "FingerTree.empty_correct"}   


    \underline{@{term_type "FingerTree.annot"}}\\
        Return sum of all annotations ($O(1)$)\\ 
    {\bf Spec} \<open>FingerTree.annot_correct\<close>:
    @{thm [display] "FingerTree.annot_correct"}   


    \underline{@{term_type "FingerTree.toTree"}}\\
        Convert list to finger tree ($O(n\log(n))$)\\
    {\bf Spec} \<open>FingerTree.toTree_correct\<close>:  
    @{thm [display] "FingerTree.toTree_correct"}     


    \underline{@{term_type "FingerTree.lcons"}}\\
        Append element at the left end ($O(\log(n))$, $O(1)$ amortized)\\                                                            
    {\bf Spec} \<open>FingerTree.lcons_correct\<close>:                                                                                   
    @{thm [display] "FingerTree.lcons_correct"}                                                                                      
                                                                                                                     
                                                                                                                     
    \underline{@{term_type "FingerTree.rcons"}}\\                                                                    
        Append element at the right end ($O(\log(n))$, $O(1)$ amortized)\\                                           
    {\bf Spec} \<open>FingerTree.rcons_correct\<close>:                                                                   
    @{thm [display] "FingerTree.rcons_correct"}                                                                      
                                                                                                                     
                                                                                                                     
    \underline{@{term_type "FingerTree.viewL"}}\\                                                                    
        Detach leftmost element ($O(\log(n))$, $O(1)$ amortized)\\                                                   
    {\bf Spec} \<open>FingerTree.viewL_correct\<close>:                                                                   
    @{thm [display] "FingerTree.viewL_correct"}                                                                      
                                                                                                                     

    \underline{@{term_type "FingerTree.viewR"}}\\
        Detach rightmost element ($O(\log(n))$, $O(1)$ amortized)\\
    {\bf Spec} \<open>FingerTree.viewR_correct\<close>:                 
    @{thm [display] "FingerTree.viewR_correct"}                    


    \underline{@{term_type "FingerTree.isEmpty"}}\\
        Check whether tree is empty ($O(1)$)\\     
    {\bf Spec} \<open>FingerTree.isEmpty_correct\<close>:
    @{thm [display] "FingerTree.isEmpty_correct"}   


    \underline{@{term_type "FingerTree.head"}}\\
        Get leftmost element of non-empty tree ($O(\log(n))$)\\
    {\bf Spec} \<open>FingerTree.head_correct\<close>:              
    @{thm [display] "FingerTree.head_correct"}                 


    \underline{@{term_type "FingerTree.tail"}}\\
        Get all but leftmost element of non-empty tree ($O(\log(n))$)\\
    {\bf Spec} \<open>FingerTree.tail_correct\<close>:                      
    @{thm [display] "FingerTree.tail_correct"}                         


    \underline{@{term_type "FingerTree.headR"}}\\
        Get rightmost element of non-empty tree ($O(\log(n))$)\\
    {\bf Spec} \<open>FingerTree.headR_correct\<close>:              
    @{thm [display] "FingerTree.headR_correct"}                 


    \underline{@{term_type "FingerTree.tailR"}}\\
        Get all but rightmost element of non-empty tree ($O(\log(n))$)\\
    {\bf Spec} \<open>FingerTree.tailR_correct\<close>:
    @{thm [display] "FingerTree.tailR_correct"}


    \underline{@{term_type "FingerTree.app"}}\\
        Concatenate two finger trees ($O(\log(m+n))$)\\
    {\bf Spec} \<open>FingerTree.app_correct\<close>:
    @{thm [display] "FingerTree.app_correct"}


    \underline{@{term "FingerTree.splitTree"}}
    @{term_type [display] "FingerTree.splitTree"}
        Split tree by a monotone predicate. ($O(\log(n))$)

    A predicate $p$ over the annotations is called monotone, iff, for all
    annotations
    $a,b$ with $p(a)$, we have already $p(a+b)$.

    Splitting is done by specifying a monotone predicate $p$ that does not hold
    for the initial value $i$ of the summation, but holds for $i$ plus the sum
    of all annotations. The tree is then split at the position where $p$ starts to
    hold for the sum of all elements up to that position.\\
    {\bf Spec} \<open>FingerTree.splitTree_correct\<close>:
    @{thm [display] "FingerTree.splitTree_correct"}


    \underline{@{term "FingerTree.foldl"}}
    @{term_type [display] "FingerTree.foldl"}
        Fold with function from left\\
    {\bf Spec} \<open>FingerTree.foldl_correct\<close>:
    @{thm [display] "FingerTree.foldl_correct"}


    \underline{@{term "FingerTree.foldr"}}
    @{term_type [display] "FingerTree.foldr"}
        Fold with function from right\\
    {\bf Spec} \<open>FingerTree.foldr_correct\<close>:
    @{thm [display] "FingerTree.foldr_correct"}


    \underline{@{term_type "FingerTree.count"}}\\
        Return the number of elements\\
    {\bf Spec} \<open>FingerTree.count_correct\<close>:
    @{thm [display] "FingerTree.count_correct"}
\<close>

end
