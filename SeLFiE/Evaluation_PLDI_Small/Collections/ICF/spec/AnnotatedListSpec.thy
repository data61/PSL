section \<open>\isaheader{Specification of Annotated Lists}\<close>
theory AnnotatedListSpec
imports ICF_Spec_Base
begin

(*@intf AnnotatedList
  @abstype ('e \<times> 'a::monoid_add) list
  Lists with annotated elements. The annotations form a monoid, and there is
  a split operation to split the list according to its annotations. This is the
  abstract concept implemented by finger trees.
*)

subsection "Introduction"
text \<open>
  We define lists with annotated elements. The annotations form a monoid.

  We provide standard list operations and the split-operation, that
  splits the list according to its annotations.
\<close>
locale al =
  \<comment> \<open>Annotated lists are abstracted to lists of pairs of elements and annotations.\<close>
  fixes \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes invar :: "'s \<Rightarrow> bool"
  
locale al_no_invar = al +
  assumes invar[simp, intro!]: "\<And>l. invar l"

subsection "Basic Annotated List Operations"

subsubsection "Empty Annotated List"
locale al_empty = al +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes empty :: "unit \<Rightarrow> 's"
  assumes empty_correct: 
    "invar (empty ())" 
    "\<alpha> (empty ()) = Nil" 

subsubsection "Emptiness Check"
locale al_isEmpty = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct: 
    "invar s \<Longrightarrow> isEmpty s \<longleftrightarrow> \<alpha> s = Nil" 

subsubsection "Counting Elements"
locale al_count = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes count :: "'s \<Rightarrow> nat"
  assumes count_correct: 
    "invar s \<Longrightarrow> count s = length(\<alpha> s)" 

subsubsection "Appending an Element from the Left"
locale al_consl = al +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes consl :: "'e \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's"
  assumes consl_correct:
    "invar s \<Longrightarrow> invar (consl e a s)"
    "invar s \<Longrightarrow> (\<alpha> (consl e a s)) = (e,a) # (\<alpha> s)"

subsubsection "Appending an Element from the Right"
locale al_consr = al +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes consr :: "'s \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 's"
  assumes consr_correct:
    "invar s \<Longrightarrow> invar (consr s e a)"
    "invar s \<Longrightarrow> (\<alpha> (consr s e a)) = (\<alpha> s) @ [(e,a)]"
  
subsubsection "Take the First Element"
locale al_head = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes head :: "'s \<Rightarrow> ('e \<times> 'a)"
  assumes head_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> Nil\<rbrakk> \<Longrightarrow> head s = hd (\<alpha> s)"

subsubsection "Drop the First Element"
locale al_tail = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes tail :: "'s \<Rightarrow> 's"
  assumes tail_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> Nil\<rbrakk> \<Longrightarrow> \<alpha> (tail s) = tl (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> Nil\<rbrakk> \<Longrightarrow> invar (tail s)"

subsubsection "Take the Last Element"
locale al_headR = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes headR :: "'s \<Rightarrow> ('e \<times> 'a)"
  assumes headR_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> Nil\<rbrakk> \<Longrightarrow> headR s = last (\<alpha> s)"

subsubsection "Drop the Last Element"
locale al_tailR = al +   
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes tailR :: "'s \<Rightarrow> 's"
  assumes tailR_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> Nil\<rbrakk> \<Longrightarrow> \<alpha> (tailR s) = butlast (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> Nil\<rbrakk> \<Longrightarrow> invar (tailR s)"

subsubsection "Fold a Function over the Elements from the Left"
locale al_foldl = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes foldl :: "('z \<Rightarrow> 'e \<times> 'a \<Rightarrow> 'z) \<Rightarrow> 'z \<Rightarrow> 's \<Rightarrow> 'z"
  assumes foldl_correct:
    "invar s \<Longrightarrow> foldl f \<sigma> s = List.foldl f \<sigma> (\<alpha> s)"

subsubsection "Fold a Function over the Elements from the Right"
locale al_foldr = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes foldr :: "('e \<times> 'a \<Rightarrow> 'z \<Rightarrow> 'z) \<Rightarrow> 's \<Rightarrow> 'z \<Rightarrow> 'z"
  assumes foldr_correct:
    "invar s \<Longrightarrow> foldr f s \<sigma> = List.foldr f (\<alpha> s) \<sigma>"

locale poly_al_fold = al +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
begin
  definition foldl where 
    foldl_correct[code_unfold]: "foldl f \<sigma> s = List.foldl f \<sigma> (\<alpha> s)"
  definition foldr where 
    foldr_correct[code_unfold]: "foldr f s \<sigma> = List.foldr f (\<alpha> s) \<sigma>"
end
    
subsubsection "Concatenation of Two Annotated Lists"
locale al_app = al +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes app :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  assumes app_correct:
    "\<lbrakk>invar s;invar s'\<rbrakk> \<Longrightarrow> \<alpha> (app s s') = (\<alpha> s) @ (\<alpha> s')"
    "\<lbrakk>invar s;invar s'\<rbrakk> \<Longrightarrow> invar (app s s')"

subsubsection "Readout the Summed up Annotations"
locale al_annot = al +
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes annot :: "'s \<Rightarrow> 'a"
  assumes annot_correct:
    "invar s \<Longrightarrow> (annot s) = (sum_list (map snd (\<alpha> s)))"

subsubsection "Split by Monotone Predicate"
locale al_splits = al + 
  constrains \<alpha> :: "'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  fixes splits :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 
                                ('s \<times> ('e \<times> 'a) \<times> 's)"
  assumes splits_correct:
    "\<lbrakk>invar s;
       \<forall>a b. p a \<longrightarrow> p (a + b);
       \<not> p i; 
       p (i + sum_list (map snd (\<alpha> s)));
       (splits p i s) = (l, (e,a), r)\<rbrakk> 
      \<Longrightarrow> 
        (\<alpha> s) = (\<alpha> l) @ (e,a) # (\<alpha> r)  \<and>
        \<not> p (i + sum_list (map snd (\<alpha> l)))  \<and>
        p (i + sum_list (map snd (\<alpha> l)) + a)  \<and>
        invar l  \<and>
        invar r
    "
begin
  lemma splitsE:
    assumes 
    invar: "invar s" and
    mono: "\<forall>a b. p a \<longrightarrow> p (a + b)" and
    init_ff: "\<not> p i" and
    sum_tt: "p (i + sum_list (map snd (\<alpha> s)))"
    obtains l e a r where
    "(splits p i s) = (l, (e,a), r)"
    "(\<alpha> s) = (\<alpha> l) @ (e,a) # (\<alpha> r)"
    "\<not> p (i + sum_list (map snd (\<alpha> l)))"
    "p (i + sum_list (map snd (\<alpha> l)) + a)"
    "invar l"
    "invar r"
    using assms
    apply (cases "splits p i s")
    apply (case_tac b)
    apply (drule_tac i = i and p = p 
      and l = a and r = c and e = aa and a = ba in  splits_correct)
    apply (simp_all)
    done
end    

subsection "Record Based Interface"
record ('e,'a,'s) alist_ops =
  alist_op_\<alpha> ::"'s \<Rightarrow> ('e \<times> 'a::monoid_add) list"
  alist_op_invar :: "'s \<Rightarrow> bool"
  alist_op_empty :: "unit \<Rightarrow> 's"
  alist_op_isEmpty :: "'s \<Rightarrow> bool"
  alist_op_count :: "'s \<Rightarrow> nat"
  alist_op_consl :: "'e \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> 's"
  alist_op_consr :: "'s \<Rightarrow> 'e \<Rightarrow> 'a \<Rightarrow> 's"
  alist_op_head :: "'s \<Rightarrow> ('e \<times> 'a)"
  alist_op_tail :: "'s \<Rightarrow> 's"
  alist_op_headR :: "'s \<Rightarrow> ('e \<times> 'a)"
  alist_op_tailR :: "'s \<Rightarrow> 's"
  alist_op_app :: "'s \<Rightarrow> 's \<Rightarrow> 's"
  alist_op_annot :: "'s \<Rightarrow> 'a"
  alist_op_splits :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> ('s \<times> ('e \<times> 'a) \<times> 's)"

locale StdALDefs = poly_al_fold "alist_op_\<alpha> ops" "alist_op_invar ops"
  for ops :: "('e,'a::monoid_add,'s,'more) alist_ops_scheme"
begin
  abbreviation \<alpha> where "\<alpha> == alist_op_\<alpha> ops"
  abbreviation invar where "invar == alist_op_invar ops "
  abbreviation empty where "empty == alist_op_empty ops "
  abbreviation isEmpty where "isEmpty == alist_op_isEmpty ops "
  abbreviation count where "count == alist_op_count ops"
  abbreviation consl where "consl == alist_op_consl ops "
  abbreviation consr where "consr == alist_op_consr ops "
  abbreviation head where "head == alist_op_head ops "
  abbreviation tail where "tail == alist_op_tail ops "
  abbreviation headR where "headR == alist_op_headR ops "
  abbreviation tailR where "tailR == alist_op_tailR ops "
  abbreviation app where "app == alist_op_app ops "
  abbreviation annot where "annot == alist_op_annot ops "
  abbreviation splits where "splits == alist_op_splits ops "
end

locale StdAL = StdALDefs ops +
  al \<alpha> invar +
  al_empty \<alpha> invar empty +
  al_isEmpty \<alpha> invar isEmpty +
  al_count \<alpha> invar count +
  al_consl \<alpha> invar consl +
  al_consr \<alpha> invar consr +
  al_head \<alpha> invar head +
  al_tail \<alpha> invar tail +
  al_headR \<alpha> invar headR +
  al_tailR \<alpha> invar tailR +
  al_app \<alpha> invar app +
  al_annot \<alpha> invar annot +
  al_splits \<alpha> invar splits
  for ops
begin
  lemmas correct =
    empty_correct 
    isEmpty_correct
    count_correct
    consl_correct
    consr_correct
    head_correct
    tail_correct
    headR_correct
    tailR_correct
    app_correct
    annot_correct      
    foldl_correct
    foldr_correct
end

locale StdAL_no_invar = StdAL + al_no_invar \<alpha> invar


end
