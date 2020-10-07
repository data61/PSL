(***********************************************************************************
 * Copyright (c) 2016-2018 The University of Sheffield, UK
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 *
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 * 
 * SPDX-License-Identifier: BSD-2-Clause
 ***********************************************************************************)

section\<open>CharacterData\<close>
text\<open>In this theory, we introduce the typed pointers for the class CharacterData.\<close>   
theory CharacterDataPointer
  imports
    ElementPointer
begin

datatype 'character_data_ptr character_data_ptr = Ref (the_ref: ref) | Ext 'character_data_ptr
register_default_tvars "'character_data_ptr character_data_ptr" 
type_synonym ('node_ptr, 'element_ptr, 'character_data_ptr) node_ptr
  = "('character_data_ptr character_data_ptr + 'node_ptr, 'element_ptr) node_ptr"
register_default_tvars "('node_ptr, 'element_ptr, 'character_data_ptr) node_ptr" 
type_synonym ('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr) object_ptr
  = "('object_ptr, 'character_data_ptr character_data_ptr + 'node_ptr, 'element_ptr) object_ptr"
register_default_tvars "('object_ptr, 'node_ptr, 'element_ptr, 'character_data_ptr) object_ptr" 

definition cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) character_data_ptr \<Rightarrow> (_) node_ptr"
  where
    "cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr = node_ptr.Ext (Inr (Inl ptr))"

abbreviation cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) character_data_ptr \<Rightarrow> (_) object_ptr"
  where
    "cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr)"

definition cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) node_ptr \<Rightarrow> (_) character_data_ptr option"
  where
    "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = (case node_ptr of 
                        node_ptr.Ext (Inr (Inl character_data_ptr)) \<Rightarrow> Some character_data_ptr
                       | _ \<Rightarrow> None)"

abbreviation cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) object_ptr \<Rightarrow> (_) character_data_ptr option"
  where
    "cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
                               Some node_ptr \<Rightarrow> cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr
                             | None \<Rightarrow> None)"

adhoc_overloading cast cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r 
  cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r

consts is_character_data_ptr_kind :: 'a
definition is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) node_ptr \<Rightarrow> bool"
  where
    "is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr = (case cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr 
                                             of Some _ \<Rightarrow> True | _ \<Rightarrow> False)"

abbreviation is_character_data_ptr_kind\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) object_ptr \<Rightarrow> bool"
  where
    "is_character_data_ptr_kind\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> (case cast ptr of 
                        Some node_ptr \<Rightarrow> is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr
                      | None \<Rightarrow> False)"

adhoc_overloading is_character_data_ptr_kind is_character_data_ptr_kind\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r 
  is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r
lemmas is_character_data_ptr_kind_def = is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def

consts is_character_data_ptr :: 'a
definition is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) character_data_ptr \<Rightarrow> bool"
  where
    "is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr = (case ptr 
                                 of character_data_ptr.Ref _ \<Rightarrow> True | _ \<Rightarrow> False)"

abbreviation is_character_data_ptr\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) node_ptr \<Rightarrow> bool"
  where
    "is_character_data_ptr\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> (case cast ptr of
      Some character_data_ptr \<Rightarrow> is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr
    | _ \<Rightarrow> False)"

abbreviation is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r :: "(_) object_ptr \<Rightarrow> bool"
  where
    "is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
      Some node_ptr \<Rightarrow> is_character_data_ptr\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr
    | None \<Rightarrow> False)"

adhoc_overloading is_character_data_ptr
  is_character_data_ptr\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r is_character_data_ptr\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r
lemmas is_character_data_ptr_def = is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def

consts is_character_data_ptr_ext :: 'a
abbreviation 
  "is_character_data_ptr_ext\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> \<not> is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr"

abbreviation "is_character_data_ptr_ext\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> (case cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
  Some character_data_ptr \<Rightarrow> is_character_data_ptr_ext\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr
| None \<Rightarrow> False)"

abbreviation "is_character_data_ptr_ext\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr \<equiv> (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
  Some node_ptr \<Rightarrow> is_character_data_ptr_ext\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr
| None \<Rightarrow> False)"

adhoc_overloading is_character_data_ptr_ext
  is_character_data_ptr_ext\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r is_character_data_ptr_ext\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r is_character_data_ptr_ext\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r

instantiation character_data_ptr :: (linorder) linorder
begin
definition 
  less_eq_character_data_ptr :: "(_::linorder) character_data_ptr \<Rightarrow> (_) character_data_ptr \<Rightarrow> bool"
  where 
    "less_eq_character_data_ptr x y \<equiv> (case x of Ext i \<Rightarrow> (case y of Ext j \<Rightarrow> i \<le> j | Ref _ \<Rightarrow> False)
                                               | Ref i \<Rightarrow> (case y of Ext _ \<Rightarrow> True | Ref j \<Rightarrow> i \<le> j))"
definition 
  less_character_data_ptr :: "(_::linorder) character_data_ptr \<Rightarrow> (_) character_data_ptr \<Rightarrow> bool"
  where "less_character_data_ptr x y \<equiv> x \<le> y \<and> \<not> y \<le> x"
instance 
  apply(standard) 
  by(auto simp add: less_eq_character_data_ptr_def less_character_data_ptr_def 
      split: character_data_ptr.splits)
end

lemma is_character_data_ptr_ref [simp]: "is_character_data_ptr (character_data_ptr.Ref n)"
  by(simp add: is_character_data_ptr\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)

lemma cast_element_ptr_not_character_data_ptr [simp]:
  "(cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr \<noteq> cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr)"
  "(cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr \<noteq> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr)"
  unfolding cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def 
  by(auto)

lemma is_character_data_ptr_kind_not_element_ptr [simp]: 
  "\<not> is_character_data_ptr_kind (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr)"
  unfolding is_character_data_ptr_kind_def cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
  by auto
lemma is_element_ptr_kind_not_character_data_ptr [simp]: 
  "\<not> is_element_ptr_kind (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr)"
  using is_element_ptr_kind_obtains by fastforce

lemma is_character_data_ptr_kind\<^sub>_cast [simp]: 
  "is_character_data_ptr_kind (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr)"
  by (simp add: cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def 
      is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)

lemma character_data_ptr_casts_commute [simp]:
  "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = Some character_data_ptr
   \<longleftrightarrow> cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr = node_ptr"
  unfolding cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
  by(auto split: node_ptr.splits sum.splits)

lemma character_data_ptr_casts_commute2 [simp]:
  "(cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r (cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr) = Some character_data_ptr)"
  by simp

lemma character_data_ptr_casts_commute3 [simp]:
  assumes "is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr"
  shows "cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r (the (cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr)) = node_ptr"
  using assms
  by(auto simp add: is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def 
      cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
      split: node_ptr.splits sum.splits)

lemma is_character_data_ptr_kind_obtains:
  assumes "is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr"
  obtains character_data_ptr where "cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r character_data_ptr = node_ptr"
  by (metis assms is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def case_optionE 
      character_data_ptr_casts_commute)

lemma is_character_data_ptr_kind_none:
  assumes "\<not>is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr"
  shows "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r node_ptr = None"
  using assms
  unfolding is_character_data_ptr_kind\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def
  by(auto split: node_ptr.splits sum.splits)

lemma cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_inject [simp]: 
  "cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r x = cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r y \<longleftrightarrow> x = y"
  by(simp add: cast\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)

lemma cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_ext_none [simp]: 
  "cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r (node_ptr.Ext (Inr (Inr node_ext_ptr))) = None"
  by(simp add: cast\<^sub>n\<^sub>o\<^sub>d\<^sub>e\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>c\<^sub>h\<^sub>a\<^sub>r\<^sub>a\<^sub>c\<^sub>t\<^sub>e\<^sub>r\<^sub>_\<^sub>d\<^sub>a\<^sub>t\<^sub>a\<^sub>_\<^sub>p\<^sub>t\<^sub>r_def)

end
