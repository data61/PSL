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

section\<open>Testing removeChild\<close>
text\<open>This theory contains the test cases for removeChild.\<close>

theory Node_removeChild
imports
  "Core_DOM_BaseTest"
begin

definition Node_removeChild_heap :: "(unit, unit, unit, unit, unit, unit, unit, unit, unit, unit, unit) heap" where
  "Node_removeChild_heap = create_heap [(cast (document_ptr.Ref 1), cast (create_document_obj html (Some (cast (element_ptr.Ref 1))) [])),
    (cast (element_ptr.Ref 1), cast (create_element_obj ''html'' [cast (element_ptr.Ref 2), cast (element_ptr.Ref 7)] fmempty None)),
    (cast (element_ptr.Ref 2), cast (create_element_obj ''head'' [cast (element_ptr.Ref 3), cast (element_ptr.Ref 4), cast (element_ptr.Ref 5), cast (element_ptr.Ref 6)] fmempty None)),
    (cast (element_ptr.Ref 3), cast (create_element_obj ''title'' [cast (character_data_ptr.Ref 1)] fmempty None)),
    (cast (character_data_ptr.Ref 1), cast (create_character_data_obj ''Node.removeChild'')),
    (cast (element_ptr.Ref 4), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharness.js'')]) None)),
    (cast (element_ptr.Ref 5), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharnessreport.js'')]) None)),
    (cast (element_ptr.Ref 6), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''creators.js'')]) None)),
    (cast (element_ptr.Ref 7), cast (create_element_obj ''body'' [cast (element_ptr.Ref 8), cast (element_ptr.Ref 9), cast (element_ptr.Ref 10)] fmempty None)),
    (cast (element_ptr.Ref 8), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', ''log'')]) None)),
    (cast (element_ptr.Ref 9), cast (create_element_obj ''iframe'' [] (fmap_of_list [(''src'', ''about:blank'')]) None)),
    (cast (element_ptr.Ref 10), cast (create_element_obj ''script'' [cast (character_data_ptr.Ref 2)] fmempty None)),
    (cast (character_data_ptr.Ref 2), cast (create_character_data_obj ''%3C%3Cscript%3E%3E''))]"

definition document :: "(unit, unit, unit, unit, unit, unit) object_ptr option" where "document = Some (cast (document_ptr.Ref 1))"


text \<open>"Passing a detached Element to removeChild should not affect it."\<close>

lemma "test (do {
  doc \<leftarrow> return document;
  s \<leftarrow> doc . createElement(''div'');
  tmp0 \<leftarrow> s . ownerDocument;
  assert_equals(tmp0, doc);
  tmp1 \<leftarrow> document . body;
  assert_throws(NotFoundError, tmp1 . removeChild(s));
  tmp2 \<leftarrow> s . ownerDocument;
  assert_equals(tmp2, doc)
}) Node_removeChild_heap"
  by eval


text \<open>"Passing a non-detached Element to removeChild should not affect it."\<close>

lemma "test (do {
  doc \<leftarrow> return document;
  s \<leftarrow> doc . createElement(''div'');
  tmp0 \<leftarrow> doc . documentElement;
  tmp0 . appendChild(s);
  tmp1 \<leftarrow> s . ownerDocument;
  assert_equals(tmp1, doc);
  tmp2 \<leftarrow> document . body;
  assert_throws(NotFoundError, tmp2 . removeChild(s));
  tmp3 \<leftarrow> s . ownerDocument;
  assert_equals(tmp3, doc)
}) Node_removeChild_heap"
  by eval


text \<open>"Calling removeChild on an Element with no children should throw NOT\_FOUND\_ERR."\<close>

lemma "test (do {
  doc \<leftarrow> return document;
  s \<leftarrow> doc . createElement(''div'');
  tmp0 \<leftarrow> doc . body;
  tmp0 . appendChild(s);
  tmp1 \<leftarrow> s . ownerDocument;
  assert_equals(tmp1, doc);
  assert_throws(NotFoundError, s . removeChild(doc))
}) Node_removeChild_heap"
  by eval


text \<open>"Passing a detached Element to removeChild should not affect it."\<close>

lemma "test (do {
  doc \<leftarrow> createDocument('''');
  s \<leftarrow> doc . createElement(''div'');
  tmp0 \<leftarrow> s . ownerDocument;
  assert_equals(tmp0, doc);
  tmp1 \<leftarrow> document . body;
  assert_throws(NotFoundError, tmp1 . removeChild(s));
  tmp2 \<leftarrow> s . ownerDocument;
  assert_equals(tmp2, doc)
}) Node_removeChild_heap"
  by eval


text \<open>"Passing a non-detached Element to removeChild should not affect it."\<close>

lemma "test (do {
  doc \<leftarrow> createDocument('''');
  s \<leftarrow> doc . createElement(''div'');
  tmp0 \<leftarrow> doc . documentElement;
  tmp0 . appendChild(s);
  tmp1 \<leftarrow> s . ownerDocument;
  assert_equals(tmp1, doc);
  tmp2 \<leftarrow> document . body;
  assert_throws(NotFoundError, tmp2 . removeChild(s));
  tmp3 \<leftarrow> s . ownerDocument;
  assert_equals(tmp3, doc)
}) Node_removeChild_heap"
  by eval


text \<open>"Calling removeChild on an Element with no children should throw NOT\_FOUND\_ERR."\<close>

lemma "test (do {
  doc \<leftarrow> createDocument('''');
  s \<leftarrow> doc . createElement(''div'');
  tmp0 \<leftarrow> doc . body;
  tmp0 . appendChild(s);
  tmp1 \<leftarrow> s . ownerDocument;
  assert_equals(tmp1, doc);
  assert_throws(NotFoundError, s . removeChild(doc))
}) Node_removeChild_heap"
  by eval


text \<open>"Passing a value that is not a Node reference to removeChild should throw TypeError."\<close>

lemma "test (do {
  tmp0 \<leftarrow> document . body;
  assert_throws(TypeError, tmp0 . removeChild(None))
}) Node_removeChild_heap"
  by eval


end
