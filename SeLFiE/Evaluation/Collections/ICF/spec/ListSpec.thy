section \<open>\isaheader{Specification of Sequences}\<close>
theory ListSpec 
imports ICF_Spec_Base
begin

(*@intf List
  @abstype 'a list
  This interface specifies sequences.
*)

subsection "Definition"
locale list =
  \<comment> \<open>Abstraction to HOL-lists\<close>
  fixes \<alpha> :: "'s \<Rightarrow> 'x list"
  \<comment> \<open>Invariant\<close>
  fixes invar :: "'s \<Rightarrow> bool"

locale list_no_invar = list +
  assumes invar[simp, intro!]: "\<And>l. invar l"

subsection "Functions"

locale list_empty = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes empty :: "unit \<Rightarrow> 's"
  assumes empty_correct:
    "\<alpha> (empty ()) = []"
    "invar (empty ())"


locale list_isEmpty = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes isEmpty :: "'s \<Rightarrow> bool"
  assumes isEmpty_correct:
    "invar s \<Longrightarrow> isEmpty s \<longleftrightarrow> \<alpha> s = []"

locale poly_list_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
begin  
  definition iteratei where
    iteratei_correct[code_unfold]: "iteratei s \<equiv> foldli (\<alpha> s)"
  definition iterate where
    iterate_correct[code_unfold]: "iterate s \<equiv> foldli (\<alpha> s) (\<lambda>_. True)"
end

locale poly_list_rev_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
begin  
  definition rev_iteratei where
    rev_iteratei_correct[code_unfold]: "rev_iteratei s \<equiv> foldri (\<alpha> s)"
  definition rev_iterate where
    rev_iterate_correct[code_unfold]: "rev_iterate s \<equiv> foldri (\<alpha> s) (\<lambda>_. True)"
end

(*
locale list_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes iteratei :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
  assumes iteratei_correct:
    "invar s \<Longrightarrow> iteratei s = foldli (\<alpha> s)"
begin
  lemma iteratei_no_sel_rule:
    "invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> set_iterator (iteratei s) (set (\<alpha> s))"
    by (simp add: iteratei_correct set_iterator_foldli_correct)
end

lemma list_iteratei_iteratei_linord_rule:
  "list_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (\<alpha> s) \<Longrightarrow>
   set_iterator_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_iteratei_def set_iterator_linord_foldli_correct)

lemma list_iteratei_iteratei_rev_linord_rule:
  "list_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (rev (\<alpha> s)) \<Longrightarrow>
   set_iterator_rev_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_iteratei_def set_iterator_rev_linord_foldli_correct)


locale list_reverse_iteratei = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes reverse_iteratei :: "'s \<Rightarrow> ('x,'\<sigma>) set_iterator"
  assumes reverse_iteratei_correct:
    "invar s \<Longrightarrow> reverse_iteratei s = foldri (\<alpha> s)"
begin
  lemma reverse_iteratei_no_sel_rule:
    "invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> set_iterator (reverse_iteratei s) (set (\<alpha> s))"
    by (simp add: reverse_iteratei_correct set_iterator_foldri_correct)
end

lemma list_reverse_iteratei_iteratei_linord_rule:
  "list_reverse_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (rev (\<alpha> s)) \<Longrightarrow>
   set_iterator_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_reverse_iteratei_def set_iterator_linord_foldri_correct)

lemma list_reverse_iteratei_iteratei_rev_linord_rule:
  "list_reverse_iteratei \<alpha> invar iteratei \<Longrightarrow> invar s \<Longrightarrow> distinct (\<alpha> s) \<Longrightarrow> sorted (\<alpha> s) \<Longrightarrow>
   set_iterator_rev_linord (iteratei s) (set (\<alpha> s))"
  by (simp add: list_reverse_iteratei_def set_iterator_rev_linord_foldri_correct)
*)

locale list_size = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes size :: "'s \<Rightarrow> nat"
  assumes size_correct:
    "invar s \<Longrightarrow> size s = length (\<alpha> s)"
  
locale list_appendl = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes appendl :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes appendl_correct:
    "invar s \<Longrightarrow> \<alpha> (appendl x s) = x#\<alpha> s"
    "invar s \<Longrightarrow> invar (appendl x s)"
begin
  abbreviation (input) "push \<equiv> appendl" 
  lemmas push_correct = appendl_correct
end

locale list_removel = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes removel :: "'s \<Rightarrow> ('x \<times> 's)"
  assumes removel_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> fst (removel s) = hd (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (snd (removel s)) = tl (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> invar (snd (removel s))"
begin
  lemma removelE: 
    assumes I: "invar s" "\<alpha> s \<noteq> []" 
    obtains s' where "removel s = (hd (\<alpha> s), s')" "invar s'" "\<alpha> s' = tl (\<alpha> s)"
  proof -
    from removel_correct(1,2,3)[OF I] have 
      C: "fst (removel s) = hd (\<alpha> s)"
         "\<alpha> (snd (removel s)) = tl (\<alpha> s)"
         "invar (snd (removel s))" .
    from that[of "snd (removel s)", OF _ C(3,2), folded C(1)] show thesis
      by simp
  qed


  text \<open>The following shortcut notations are not meant for generating efficient code,
    but solely to simplify reasoning\<close>
  (* TODO: Is this actually used somewhere ? *)
  (*
  definition "head s == fst (removef s)"
  definition "tail s == snd (removef s)"

  lemma tail_correct: "\<lbrakk>invar F; \<alpha> F \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (tail F) = tl (\<alpha> F)"
    by (simp add: tail_def removef_correct)

  lemma head_correct: "\<lbrakk>invar F; \<alpha> F \<noteq> []\<rbrakk> \<Longrightarrow> (head F) = hd (\<alpha> F)"
    by (simp add: head_def removef_correct)

  lemma removef_split: "removef F = (head F, tail F)"
    apply (cases "removef F")
    apply (simp add: head_def tail_def)
    done
    *)
      
  abbreviation (input) "pop \<equiv> removel"
  lemmas pop_correct = removel_correct

  abbreviation (input) "dequeue \<equiv> removel"
  lemmas dequeue_correct = removel_correct
end

locale list_leftmost = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes leftmost :: "'s \<Rightarrow> 'x"
  assumes leftmost_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> leftmost s = hd (\<alpha> s)"
begin
  abbreviation (input) top where "top \<equiv> leftmost"
  lemmas top_correct = leftmost_correct
end

locale list_appendr = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes appendr :: "'x \<Rightarrow> 's \<Rightarrow> 's"
  assumes appendr_correct: 
    "invar s \<Longrightarrow> \<alpha> (appendr x s) = \<alpha> s @ [x]"
    "invar s \<Longrightarrow> invar (appendr x s)"
begin
  abbreviation (input) "enqueue \<equiv> appendr"
  lemmas enqueue_correct = appendr_correct
end

locale list_remover = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes remover :: "'s \<Rightarrow> 's \<times> 'x"
  assumes remover_correct: 
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> \<alpha> (fst (remover s)) = butlast (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> snd (remover s) = last (\<alpha> s)"
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> invar (fst (remover s))"

locale list_rightmost = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes rightmost :: "'s \<Rightarrow> 'x"
  assumes rightmost_correct:
    "\<lbrakk>invar s; \<alpha> s \<noteq> []\<rbrakk> \<Longrightarrow> rightmost s = List.last (\<alpha> s)"
begin
  abbreviation (input) bot where "bot \<equiv> rightmost"
  lemmas bot_correct = rightmost_correct
end

subsubsection "Indexing"
locale list_get = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes get :: "'s \<Rightarrow> nat \<Rightarrow> 'x"
  assumes get_correct:
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> get s i = \<alpha> s ! i"

locale list_set = list +
  constrains \<alpha> :: "'s \<Rightarrow> 'x list"
  fixes set :: "'s \<Rightarrow> nat \<Rightarrow> 'x \<Rightarrow> 's"
  assumes set_correct:
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> \<alpha> (set s i x) = (\<alpha> s) [i := x]"
    "\<lbrakk>invar s; i<length (\<alpha> s)\<rbrakk> \<Longrightarrow> invar (set s i x)"

record ('a,'s) list_ops = 
  list_op_\<alpha> :: "'s \<Rightarrow> 'a list"
  list_op_invar :: "'s \<Rightarrow> bool"
  list_op_empty :: "unit \<Rightarrow> 's"
  list_op_isEmpty :: "'s \<Rightarrow> bool"
  list_op_size :: "'s \<Rightarrow> nat"
  list_op_appendl :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  list_op_removel :: "'s \<Rightarrow> 'a \<times> 's"
  list_op_leftmost :: "'s \<Rightarrow> 'a"
  list_op_appendr :: "'a \<Rightarrow> 's \<Rightarrow> 's"
  list_op_remover :: "'s \<Rightarrow> 's \<times> 'a"
  list_op_rightmost :: "'s \<Rightarrow> 'a"
  list_op_get :: "'s \<Rightarrow> nat \<Rightarrow> 'a"
  list_op_set :: "'s \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 's"

locale StdListDefs = 
  poly_list_iteratei "list_op_\<alpha> ops" "list_op_invar ops"
  + poly_list_rev_iteratei "list_op_\<alpha> ops" "list_op_invar ops"
  for ops :: "('a,'s,'more) list_ops_scheme"
begin
  abbreviation \<alpha> where "\<alpha> \<equiv> list_op_\<alpha> ops"
  abbreviation invar where "invar \<equiv> list_op_invar ops"
  abbreviation empty where "empty \<equiv> list_op_empty ops"
  abbreviation isEmpty where "isEmpty \<equiv> list_op_isEmpty ops"
  abbreviation size where "size \<equiv> list_op_size ops"
  abbreviation appendl where "appendl \<equiv> list_op_appendl ops"
  abbreviation removel where "removel \<equiv> list_op_removel ops"
  abbreviation leftmost where "leftmost \<equiv> list_op_leftmost ops"
  abbreviation appendr where "appendr \<equiv> list_op_appendr ops"
  abbreviation remover where "remover \<equiv> list_op_remover ops"
  abbreviation rightmost where "rightmost \<equiv> list_op_rightmost ops"
  abbreviation get where "get \<equiv> list_op_get ops"
  abbreviation set where "set \<equiv> list_op_set ops"
end

locale StdList = StdListDefs ops
  + list \<alpha> invar
  + list_empty \<alpha> invar empty 
  + list_isEmpty \<alpha> invar isEmpty 
  + list_size \<alpha> invar size 
  + list_appendl \<alpha> invar appendl 
  + list_removel \<alpha> invar removel 
  + list_leftmost \<alpha> invar leftmost 
  + list_appendr \<alpha> invar appendr 
  + list_remover \<alpha> invar remover 
  + list_rightmost \<alpha> invar rightmost 
  + list_get \<alpha> invar get 
  + list_set \<alpha> invar set 
  for ops :: "('a,'s,'more) list_ops_scheme"
begin
  lemmas correct = 
    empty_correct
    isEmpty_correct
    size_correct
    appendl_correct
    removel_correct
    leftmost_correct
    appendr_correct
    remover_correct
    rightmost_correct
    get_correct
    set_correct

end

locale StdList_no_invar = StdList + list_no_invar \<alpha> invar
    
end
