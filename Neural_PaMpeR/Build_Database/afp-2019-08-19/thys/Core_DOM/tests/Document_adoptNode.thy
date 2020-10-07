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

section\<open>Testing adoptNode\<close>
text\<open>This theory contains the test cases for adoptNode.\<close>

theory Document_adoptNode
imports
  "Core_DOM_BaseTest"
begin

definition Document_adoptNode_heap :: "(unit, unit, unit, unit, unit, unit, unit, unit, unit, unit, unit) heap" where
  "Document_adoptNode_heap = create_heap [(cast (document_ptr.Ref 1), cast (create_document_obj html (Some (cast (element_ptr.Ref 1))) [])),
    (cast (element_ptr.Ref 1), cast (create_element_obj ''html'' [cast (element_ptr.Ref 2), cast (element_ptr.Ref 8)] fmempty None)),
    (cast (element_ptr.Ref 2), cast (create_element_obj ''head'' [cast (element_ptr.Ref 3), cast (element_ptr.Ref 4), cast (element_ptr.Ref 5), cast (element_ptr.Ref 6), cast (element_ptr.Ref 7)] fmempty None)),
    (cast (element_ptr.Ref 3), cast (create_element_obj ''meta'' [] (fmap_of_list [(''charset'', ''utf-8'')]) None)),
    (cast (element_ptr.Ref 4), cast (create_element_obj ''title'' [cast (character_data_ptr.Ref 1)] fmempty None)),
    (cast (character_data_ptr.Ref 1), cast (create_character_data_obj ''Document.adoptNode'')),
    (cast (element_ptr.Ref 5), cast (create_element_obj ''link'' [] (fmap_of_list [(''rel'', ''help''), (''href'', ''https://dom.spec.whatwg.org/#dom-document-adoptnode'')]) None)),
    (cast (element_ptr.Ref 6), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharness.js'')]) None)),
    (cast (element_ptr.Ref 7), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharnessreport.js'')]) None)),
    (cast (element_ptr.Ref 8), cast (create_element_obj ''body'' [cast (element_ptr.Ref 9), cast (element_ptr.Ref 10), cast (element_ptr.Ref 11)] fmempty None)),
    (cast (element_ptr.Ref 9), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', ''log'')]) None)),
    (cast (element_ptr.Ref 10), cast (create_element_obj ''x<'' [cast (character_data_ptr.Ref 2)] fmempty None)),
    (cast (character_data_ptr.Ref 2), cast (create_character_data_obj ''x'')),
    (cast (element_ptr.Ref 11), cast (create_element_obj ''script'' [cast (character_data_ptr.Ref 3)] fmempty None)),
    (cast (character_data_ptr.Ref 3), cast (create_character_data_obj ''%3C%3Cscript%3E%3E''))]"

definition document :: "(unit, unit, unit, unit, unit, unit) object_ptr option" where "document = Some (cast (document_ptr.Ref 1))"


text \<open>"Adopting an Element called 'x<' should work."\<close>

lemma "test (do {
  tmp0 \<leftarrow> document . getElementsByTagName(''x<'');
  y \<leftarrow> return (tmp0 ! 0);
  child \<leftarrow> y . firstChild;
  tmp1 \<leftarrow> y . parentNode;
  tmp2 \<leftarrow> document . body;
  assert_equals(tmp1, tmp2);
  tmp3 \<leftarrow> y . ownerDocument;
  assert_equals(tmp3, document);
  tmp4 \<leftarrow> document . adoptNode(y);
  assert_equals(tmp4, y);
  tmp5 \<leftarrow> y . parentNode;
  assert_equals(tmp5, None);
  tmp6 \<leftarrow> y . firstChild;
  assert_equals(tmp6, child);
  tmp7 \<leftarrow> y . ownerDocument;
  assert_equals(tmp7, document);
  tmp8 \<leftarrow> child . ownerDocument;
  assert_equals(tmp8, document);
  doc \<leftarrow> createDocument(None, None, None);
  tmp9 \<leftarrow> doc . adoptNode(y);
  assert_equals(tmp9, y);
  tmp10 \<leftarrow> y . parentNode;
  assert_equals(tmp10, None);
  tmp11 \<leftarrow> y . firstChild;
  assert_equals(tmp11, child);
  tmp12 \<leftarrow> y . ownerDocument;
  assert_equals(tmp12, doc);
  tmp13 \<leftarrow> child . ownerDocument;
  assert_equals(tmp13, doc)
}) Document_adoptNode_heap"
  by eval


text \<open>"Adopting an Element called ':good:times:' should work."\<close>

lemma "test (do {
  x \<leftarrow> document . createElement('':good:times:'');
  tmp0 \<leftarrow> document . adoptNode(x);
  assert_equals(tmp0, x);
  doc \<leftarrow> createDocument(None, None, None);
  tmp1 \<leftarrow> doc . adoptNode(x);
  assert_equals(tmp1, x);
  tmp2 \<leftarrow> x . parentNode;
  assert_equals(tmp2, None);
  tmp3 \<leftarrow> x . ownerDocument;
  assert_equals(tmp3, doc)
}) Document_adoptNode_heap"
  by eval


end
