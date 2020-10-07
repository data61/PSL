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

section\<open>Common Test Setup\<close>
text\<open>This theory provides the common test setup that is used by all formalized test cases.\<close>

theory Core_DOM_BaseTest
  imports
  (*<*) 
  "../preliminaries/Testing_Utils"
  (*>*) 
  "../Core_DOM"
begin

definition "assert_throws e p = do {
  h \<leftarrow> get_heap;
  (if (h \<turnstile> p \<rightarrow>\<^sub>e e) then return () else error AssertException)
}"
notation assert_throws ("assert'_throws'(_, _')")

definition "test p h \<longleftrightarrow> h \<turnstile> ok p"


definition field_access :: "(string \<Rightarrow> (_, (_) object_ptr option) dom_prog) \<Rightarrow> string 
                                    \<Rightarrow> (_, (_) object_ptr option) dom_prog"  (infix "." 80)
  where
    "field_access m field = m field"

definition assert_equals :: "'a \<Rightarrow> 'a \<Rightarrow> (_, unit) dom_prog"
  where
    "assert_equals l r = (if l = r then return () else error AssertException)"
definition assert_equals_with_message :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> (_, unit) dom_prog"
  where
    "assert_equals_with_message l r _ = (if l = r then return () else error AssertException)"
notation assert_equals ("assert'_equals'(_, _')")
notation assert_equals_with_message ("assert'_equals'(_, _, _')")
notation assert_equals ("assert'_array'_equals'(_, _')")
notation assert_equals_with_message ("assert'_array'_equals'(_, _, _')")

definition assert_not_equals :: "'a \<Rightarrow> 'a \<Rightarrow> (_, unit) dom_prog"
  where
    "assert_not_equals l r = (if l \<noteq> r then return () else error AssertException)"
definition assert_not_equals_with_message :: "'a \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> (_, unit) dom_prog"
  where
    "assert_not_equals_with_message l r _ = (if l \<noteq> r then return () else error AssertException)"
notation assert_not_equals ("assert'_not'_equals'(_, _')")
notation assert_not_equals_with_message ("assert'_not'_equals'(_, _, _')")
notation assert_not_equals ("assert'_array'_not'_equals'(_, _')")
notation assert_not_equals_with_message ("assert'_array'_not'_equals'(_, _, _')")

definition removeWhiteSpaceOnlyTextNodes :: "((_) object_ptr option) \<Rightarrow> (_, unit) dom_prog"
  where
    "removeWhiteSpaceOnlyTextNodes _ = return ()"


subsection \<open>create\_heap\<close>

(* We use this construction because partially applied functions such as "map_of xs" don't play
   well together with the code generator. *)
definition "create_heap xs = Heap (fmap_of_list xs)"

code_datatype ObjectClass.heap.Heap create_heap

lemma object_ptr_kinds_code1 [code]: 
  "object_ptr_kinds (Heap (fmap_of_list xs)) = object_ptr_kinds (create_heap xs)"
  by(simp add: create_heap_def)

lemma object_ptr_kinds_code2 [code]: 
  "object_ptr_kinds (create_heap xs) = fset_of_list (map fst xs)"
  by (simp add: object_ptr_kinds_def create_heap_def dom_map_of_conv_image_fst)

lemma object_ptr_kinds_code3 [code]: 
  "fmlookup (the_heap (create_heap xs)) x = map_of xs x"
  by(auto simp add: create_heap_def fmlookup_of_list)

lemma object_ptr_kinds_code4 [code]: 
  "the_heap (create_heap xs) = fmap_of_list xs"
  by(simp add: create_heap_def)

lemma object_ptr_kinds_code5 [code]: 
  "the_heap (Heap x) = x"
  by simp

lemma object_ptr_kinds_code6 [code]: 
  "noop = return ()"
  by(simp add: noop_def)


subsection \<open>Making the functions under test compatible with untyped languages such as JavaScript\<close>

fun set_attribute_with_null :: "((_) object_ptr option) \<Rightarrow> attr_key \<Rightarrow> attr_value \<Rightarrow> (_, unit) dom_prog"
  where
    "set_attribute_with_null (Some ptr) k v = (case cast ptr of
      Some element_ptr \<Rightarrow> set_attribute element_ptr k (Some v))"
fun set_attribute_with_null2 :: "((_) object_ptr option) \<Rightarrow> attr_key \<Rightarrow> attr_value option \<Rightarrow> (_, unit) dom_prog"
  where
    "set_attribute_with_null2 (Some ptr) k v = (case cast ptr of
      Some element_ptr \<Rightarrow> set_attribute element_ptr k v)"
notation set_attribute_with_null ("_ . setAttribute'(_, _')")
notation set_attribute_with_null2 ("_ . setAttribute'(_, _')")

fun get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_with_null :: "((_) object_ptr option) \<Rightarrow> (_, (_) object_ptr option list) dom_prog"
  where
    "get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_with_null (Some ptr) = do {
      children \<leftarrow> get_child_nodes ptr;
      return (map (Some \<circ> cast) children)
    }"
notation get_child_nodes\<^sub>C\<^sub>o\<^sub>r\<^sub>e\<^sub>_\<^sub>D\<^sub>O\<^sub>M_with_null ("_ . childNodes")

fun create_element_with_null :: "((_) object_ptr option) \<Rightarrow> string \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "create_element_with_null (Some owner_document_obj) tag = (case cast owner_document_obj of
      Some owner_document \<Rightarrow> do {
        element_ptr \<leftarrow> create_element owner_document tag;
        return (Some (cast element_ptr))})"
notation create_element_with_null ("_ . createElement'(_')")

fun create_character_data_with_null :: "((_) object_ptr option) \<Rightarrow> string \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "create_character_data_with_null (Some owner_document_obj) tag = (case cast owner_document_obj of
      Some owner_document \<Rightarrow> do {
        character_data_ptr \<leftarrow> create_character_data owner_document tag;
        return (Some (cast character_data_ptr))})"
notation create_character_data_with_null ("_ . createTextNode'(_')")

definition create_document_with_null :: "string \<Rightarrow> (_, ((_::linorder) object_ptr option)) dom_prog"
  where
    "create_document_with_null title = do {
      new_document_ptr \<leftarrow> create_document;
      html \<leftarrow> create_element new_document_ptr ''html'';
      append_child (cast new_document_ptr) (cast html);
      heap \<leftarrow> create_element new_document_ptr ''heap'';
      append_child (cast html) (cast heap);
      body \<leftarrow> create_element new_document_ptr ''body'';
      append_child (cast html) (cast body);
      return (Some (cast new_document_ptr))
    }"
abbreviation "create_document_with_null2 _ _ _ \<equiv> create_document_with_null ''''"
notation create_document_with_null ("createDocument'(_')")
notation create_document_with_null2 ("createDocument'(_, _, _')")

fun get_element_by_id_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> string \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where                                                                     
    "get_element_by_id_with_null (Some ptr) id' = do {
        element_ptr_opt \<leftarrow> get_element_by_id ptr id';
        (case element_ptr_opt of
          Some element_ptr \<Rightarrow> return (Some (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr))
        | None \<Rightarrow> return None)}"
  | "get_element_by_id_with_null _ _ = error SegmentationFault"
notation get_element_by_id_with_null ("_ . getElementById'(_')")

fun get_elements_by_class_name_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> string \<Rightarrow> (_, ((_) object_ptr option) list) dom_prog"
  where                                                                     
    "get_elements_by_class_name_with_null (Some ptr) class_name =
      get_elements_by_class_name ptr class_name \<bind> map_M (return \<circ> Some \<circ> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r)"
notation get_elements_by_class_name_with_null ("_ . getElementsByClassName'(_')")

fun get_elements_by_tag_name_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> string \<Rightarrow> (_, ((_) object_ptr option) list) dom_prog"
  where                                                                     
    "get_elements_by_tag_name_with_null (Some ptr) tag_name =
      get_elements_by_tag_name ptr tag_name \<bind> map_M (return \<circ> Some \<circ> cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r)"
notation get_elements_by_tag_name_with_null ("_ . getElementsByTagName'(_')")

fun insert_before_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> ((_) object_ptr option) \<Rightarrow> ((_) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "insert_before_with_null (Some ptr) (Some child_obj) ref_child_obj_opt = (case cast child_obj of
      Some child \<Rightarrow> do {
        (case ref_child_obj_opt of
          Some ref_child_obj \<Rightarrow> insert_before ptr child (cast ref_child_obj)
        | None \<Rightarrow> insert_before ptr child None);
        return (Some child_obj)}
    | None \<Rightarrow> error HierarchyRequestError)"
notation insert_before_with_null ("_ . insertBefore'(_, _')")

fun append_child_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> ((_) object_ptr option) \<Rightarrow> (_, unit) dom_prog"
  where
    "append_child_with_null (Some ptr) (Some child_obj) = (case cast child_obj of
      Some child \<Rightarrow> append_child ptr child
    | None \<Rightarrow> error SegmentationFault)"
notation append_child_with_null ("_ . appendChild'(_')")

fun get_body :: "((_::linorder) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "get_body ptr = do {
       ptrs \<leftarrow> ptr . getElementsByTagName(''body'');
       return (hd ptrs)
    }"
notation get_body ("_ . body")

fun get_document_element_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "get_document_element_with_null (Some ptr) = (case cast\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r ptr of
    Some document_ptr \<Rightarrow> do {
      element_ptr_opt \<leftarrow> get_M document_ptr document_element;
      return (case element_ptr_opt of
        Some element_ptr \<Rightarrow> Some (cast\<^sub>e\<^sub>l\<^sub>e\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r element_ptr)
      | None \<Rightarrow> None)})"
notation get_document_element_with_null ("_ . documentElement")

fun get_owner_document_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "get_owner_document_with_null (Some ptr) = (do {
        document_ptr \<leftarrow> get_owner_document ptr;
        return (Some (cast\<^sub>d\<^sub>o\<^sub>c\<^sub>u\<^sub>m\<^sub>e\<^sub>n\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r\<^sub>2\<^sub>o\<^sub>b\<^sub>j\<^sub>e\<^sub>c\<^sub>t\<^sub>_\<^sub>p\<^sub>t\<^sub>r document_ptr))})"
notation get_owner_document_with_null ("_ . ownerDocument")

fun remove_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> ((_) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "remove_with_null (Some ptr) (Some child) = (case cast child of
      Some child_node \<Rightarrow> do {
        remove child_node;
        return (Some child)}
    | None \<Rightarrow> error NotFoundError)"
  | "remove_with_null None _ = error TypeError"
  | "remove_with_null _ None = error TypeError"
notation remove_with_null ("_ . remove'(')")

fun remove_child_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> ((_) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "remove_child_with_null (Some ptr) (Some child) = (case cast child of
      Some child_node \<Rightarrow> do {
        remove_child ptr child_node;
        return (Some child)}
    | None \<Rightarrow> error NotFoundError)"
  | "remove_child_with_null None _ = error TypeError"
  | "remove_child_with_null _ None = error TypeError"
notation remove_child_with_null ("_ . removeChild")

fun get_tag_name_with_null :: "((_) object_ptr option) \<Rightarrow> (_, attr_value) dom_prog"
  where
    "get_tag_name_with_null (Some ptr) = (case cast ptr of
      Some element_ptr \<Rightarrow> get_M element_ptr tag_type)"
notation get_tag_name_with_null ("_ . tagName")

abbreviation "remove_attribute_with_null ptr k \<equiv> set_attribute_with_null2 ptr k None"
notation remove_attribute_with_null ("_ . removeAttribute'(_')")

fun get_attribute_with_null :: "((_) object_ptr option) \<Rightarrow> attr_key \<Rightarrow> (_, attr_value option) dom_prog"
  where
    "get_attribute_with_null (Some ptr) k = (case cast ptr of 
      Some element_ptr \<Rightarrow> get_attribute element_ptr k)"
fun get_attribute_with_null2 :: "((_) object_ptr option) \<Rightarrow> attr_key \<Rightarrow> (_, attr_value) dom_prog"
  where
    "get_attribute_with_null2 (Some ptr) k = (case cast ptr of 
      Some element_ptr \<Rightarrow> do {
        a \<leftarrow> get_attribute element_ptr k;
        return (the a)})"
notation get_attribute_with_null ("_ . getAttribute'(_')")
notation get_attribute_with_null2 ("_ . getAttribute'(_')")

fun get_parent_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> (_, (_) object_ptr option) dom_prog"
  where
    "get_parent_with_null (Some ptr) = (case cast ptr of
      Some node_ptr \<Rightarrow> get_parent node_ptr)"
notation get_parent_with_null ("_ . parentNode")

fun first_child_with_null :: "((_) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "first_child_with_null (Some ptr) = do {
      child_opt \<leftarrow> first_child ptr;
      return (case child_opt of
        Some child \<Rightarrow> Some (cast child)
      | None \<Rightarrow> None)}"
notation first_child_with_null ("_ . firstChild")

fun adopt_node_with_null :: "((_::linorder) object_ptr option) \<Rightarrow> ((_) object_ptr option) \<Rightarrow> (_, ((_) object_ptr option)) dom_prog"
  where
    "adopt_node_with_null (Some ptr) (Some child) = (case cast ptr of
      Some document_ptr \<Rightarrow> (case cast child of
        Some child_node \<Rightarrow> do {
          adopt_node document_ptr child_node;
          return (Some child)}))"
notation adopt_node_with_null ("_ . adoptNode'(_')")
      

definition createTestTree :: "((_::linorder) object_ptr option) \<Rightarrow> (_, (string \<Rightarrow>  (_, ((_) object_ptr option)) dom_prog)) dom_prog"
  where
   "createTestTree ref = return (\<lambda>id. get_element_by_id_with_null ref id)"

end
