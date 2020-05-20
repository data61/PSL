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

section\<open>Testing insertBefore\<close>
text\<open>This theory contains the test cases for insertBefore.\<close>

theory Node_insertBefore
imports
  "Core_DOM_BaseTest"
begin

definition Node_insertBefore_heap :: "(unit, unit, unit, unit, unit, unit, unit, unit, unit, unit, unit) heap" where
  "Node_insertBefore_heap = create_heap [(cast (document_ptr.Ref 1), cast (create_document_obj html (Some (cast (element_ptr.Ref 1))) [])),
    (cast (element_ptr.Ref 1), cast (create_element_obj ''html'' [cast (element_ptr.Ref 2), cast (element_ptr.Ref 6)] fmempty None)),
    (cast (element_ptr.Ref 2), cast (create_element_obj ''head'' [cast (element_ptr.Ref 3), cast (element_ptr.Ref 4), cast (element_ptr.Ref 5)] fmempty None)),
    (cast (element_ptr.Ref 3), cast (create_element_obj ''title'' [cast (character_data_ptr.Ref 1)] fmempty None)),
    (cast (character_data_ptr.Ref 1), cast (create_character_data_obj ''Node.insertBefore'')),
    (cast (element_ptr.Ref 4), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharness.js'')]) None)),
    (cast (element_ptr.Ref 5), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharnessreport.js'')]) None)),
    (cast (element_ptr.Ref 6), cast (create_element_obj ''body'' [cast (element_ptr.Ref 7), cast (element_ptr.Ref 8)] fmempty None)),
    (cast (element_ptr.Ref 7), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', ''log'')]) None)),
    (cast (element_ptr.Ref 8), cast (create_element_obj ''script'' [cast (character_data_ptr.Ref 2)] fmempty None)),
    (cast (character_data_ptr.Ref 2), cast (create_character_data_obj ''%3C%3Cscript%3E%3E''))]"

definition document :: "(unit, unit, unit, unit, unit, unit) object_ptr option" where "document = Some (cast (document_ptr.Ref 1))"


text \<open>"Calling insertBefore an a leaf node Text must throw HIERARCHY\_REQUEST\_ERR."\<close>

lemma "test (do {
  node \<leftarrow> document . createTextNode(''Foo'');
  tmp0 \<leftarrow> document . createTextNode(''fail'');
  assert_throws(HierarchyRequestError, node . insertBefore(tmp0, None))
}) Node_insertBefore_heap"
  by eval


text \<open>"Calling insertBefore with an inclusive ancestor of the context object must throw HIERARCHY\_REQUEST\_ERR."\<close>

lemma "test (do {
  tmp1 \<leftarrow> document . body;
  tmp2 \<leftarrow> document . getElementById(''log'');
  tmp0 \<leftarrow> document . body;
  assert_throws(HierarchyRequestError, tmp0 . insertBefore(tmp1, tmp2));
  tmp4 \<leftarrow> document . documentElement;
  tmp5 \<leftarrow> document . getElementById(''log'');
  tmp3 \<leftarrow> document . body;
  assert_throws(HierarchyRequestError, tmp3 . insertBefore(tmp4, tmp5))
}) Node_insertBefore_heap"
  by eval


text \<open>"Calling insertBefore with a reference child whose parent is not the context node must throw a NotFoundError."\<close>

lemma "test (do {
  a \<leftarrow> document . createElement(''div'');
  b \<leftarrow> document . createElement(''div'');
  c \<leftarrow> document . createElement(''div'');
  assert_throws(NotFoundError, a . insertBefore(b, c))
}) Node_insertBefore_heap"
  by eval


text \<open>"If the context node is a document, inserting a document or text node should throw a HierarchyRequestError."\<close>

lemma "test (do {
  doc \<leftarrow> createDocument(''title'');
  doc2 \<leftarrow> createDocument(''title2'');
  tmp0 \<leftarrow> doc . documentElement;
  assert_throws(HierarchyRequestError, doc . insertBefore(doc2, tmp0));
  tmp1 \<leftarrow> doc . createTextNode(''text'');
  tmp2 \<leftarrow> doc . documentElement;
  assert_throws(HierarchyRequestError, doc . insertBefore(tmp1, tmp2))
}) Node_insertBefore_heap"
  by eval


text \<open>"Inserting a node before itself should not move the node"\<close>

lemma "test (do {
  a \<leftarrow> document . createElement(''div'');
  b \<leftarrow> document . createElement(''div'');
  c \<leftarrow> document . createElement(''div'');
  a . appendChild(b);
  a . appendChild(c);
  tmp0 \<leftarrow> a . childNodes;
  assert_array_equals(tmp0, [b, c]);
  tmp1 \<leftarrow> a . insertBefore(b, b);
  assert_equals(tmp1, b);
  tmp2 \<leftarrow> a . childNodes;
  assert_array_equals(tmp2, [b, c]);
  tmp3 \<leftarrow> a . insertBefore(c, c);
  assert_equals(tmp3, c);
  tmp4 \<leftarrow> a . childNodes;
  assert_array_equals(tmp4, [b, c])
}) Node_insertBefore_heap"
  by eval


end
