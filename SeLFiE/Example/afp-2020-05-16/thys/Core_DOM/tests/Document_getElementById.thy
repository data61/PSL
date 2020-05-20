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

section\<open>Testing getElementById\<close>
text\<open>This theory contains the test cases for getElementById.\<close>

theory Document_getElementById
imports
  "Core_DOM_BaseTest"
begin

definition Document_getElementById_heap :: "(unit, unit, unit, unit, unit, unit, unit, unit, unit, unit, unit) heap" where
  "Document_getElementById_heap = create_heap [(cast (document_ptr.Ref 1), cast (create_document_obj html (Some (cast (element_ptr.Ref 1))) [])),
    (cast (element_ptr.Ref 1), cast (create_element_obj ''html'' [cast (element_ptr.Ref 2), cast (element_ptr.Ref 9)] fmempty None)),
    (cast (element_ptr.Ref 2), cast (create_element_obj ''head'' [cast (element_ptr.Ref 3), cast (element_ptr.Ref 4), cast (element_ptr.Ref 5), cast (element_ptr.Ref 6), cast (element_ptr.Ref 7), cast (element_ptr.Ref 8)] fmempty None)),
    (cast (element_ptr.Ref 3), cast (create_element_obj ''meta'' [] (fmap_of_list [(''charset'', ''utf-8'')]) None)),
    (cast (element_ptr.Ref 4), cast (create_element_obj ''title'' [cast (character_data_ptr.Ref 1)] fmempty None)),
    (cast (character_data_ptr.Ref 1), cast (create_character_data_obj ''Document.getElementById'')),
    (cast (element_ptr.Ref 5), cast (create_element_obj ''link'' [] (fmap_of_list [(''rel'', ''author''), (''title'', ''Tetsuharu OHZEKI''), (''href'', ''mailto:saneyuki.snyk@gmail.com'')]) None)),
    (cast (element_ptr.Ref 6), cast (create_element_obj ''link'' [] (fmap_of_list [(''rel'', ''help''), (''href'', ''https://dom.spec.whatwg.org/#dom-document-getelementbyid'')]) None)),
    (cast (element_ptr.Ref 7), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharness.js'')]) None)),
    (cast (element_ptr.Ref 8), cast (create_element_obj ''script'' [] (fmap_of_list [(''src'', ''/resources/testharnessreport.js'')]) None)),
    (cast (element_ptr.Ref 9), cast (create_element_obj ''body'' [cast (element_ptr.Ref 10), cast (element_ptr.Ref 11), cast (element_ptr.Ref 12), cast (element_ptr.Ref 13), cast (element_ptr.Ref 16), cast (element_ptr.Ref 19)] fmempty None)),
    (cast (element_ptr.Ref 10), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', ''log'')]) None)),
    (cast (element_ptr.Ref 11), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', '''')]) None)),
    (cast (element_ptr.Ref 12), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', ''test1'')]) None)),
    (cast (element_ptr.Ref 13), cast (create_element_obj ''div'' [cast (element_ptr.Ref 14), cast (element_ptr.Ref 15)] (fmap_of_list [(''id'', ''test5''), (''data-name'', ''1st'')]) None)),
    (cast (element_ptr.Ref 14), cast (create_element_obj ''p'' [cast (character_data_ptr.Ref 2)] (fmap_of_list [(''id'', ''test5''), (''data-name'', ''2nd'')]) None)),
    (cast (character_data_ptr.Ref 2), cast (create_character_data_obj ''P'')),
    (cast (element_ptr.Ref 15), cast (create_element_obj ''input'' [] (fmap_of_list [(''id'', ''test5''), (''type'', ''submit''), (''value'', ''Submit''), (''data-name'', ''3rd'')]) None)),
    (cast (element_ptr.Ref 16), cast (create_element_obj ''div'' [cast (element_ptr.Ref 17)] (fmap_of_list [(''id'', ''outer'')]) None)),
    (cast (element_ptr.Ref 17), cast (create_element_obj ''div'' [cast (element_ptr.Ref 18)] (fmap_of_list [(''id'', ''middle'')]) None)),
    (cast (element_ptr.Ref 18), cast (create_element_obj ''div'' [] (fmap_of_list [(''id'', ''inner'')]) None)),
    (cast (element_ptr.Ref 19), cast (create_element_obj ''script'' [cast (character_data_ptr.Ref 3)] fmempty None)),
    (cast (character_data_ptr.Ref 3), cast (create_character_data_obj ''%3C%3Cscript%3E%3E''))]"

definition document :: "(unit, unit, unit, unit, unit, unit) object_ptr option" where "document = Some (cast (document_ptr.Ref 1))"


text \<open>"Document.getElementById with a script-inserted element"\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test2'';
  test \<leftarrow> document . createElement(''div'');
  test . setAttribute(''id'', TEST_ID);
  gBody . appendChild(test);
  result \<leftarrow> document . getElementById(TEST_ID);
  assert_not_equals(result, None, ''should not be null.'');
  tmp0 \<leftarrow> result . tagName;
  assert_equals(tmp0, ''div'', ''should have appended element's tag name'');
  gBody . removeChild(test);
  removed \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(removed, None, ''should not get removed element.'')
}) Document_getElementById_heap"
  by eval


text \<open>"update `id` attribute via setAttribute/removeAttribute"\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test3'';
  test \<leftarrow> document . createElement(''div'');
  test . setAttribute(''id'', TEST_ID);
  gBody . appendChild(test);
  UPDATED_ID \<leftarrow> return ''test3-updated'';
  test . setAttribute(''id'', UPDATED_ID);
  e \<leftarrow> document . getElementById(UPDATED_ID);
  assert_equals(e, test, ''should get the element with id.'');
  old \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(old, None, ''shouldn't get the element by the old id.'');
  test . removeAttribute(''id'');
  e2 \<leftarrow> document . getElementById(UPDATED_ID);
  assert_equals(e2, None, ''should return null when the passed id is none in document.'')
}) Document_getElementById_heap"
  by eval


text \<open>"Ensure that the id attribute only affects elements present in a document"\<close>

lemma "test (do {
  TEST_ID \<leftarrow> return ''test4-should-not-exist'';
  e \<leftarrow> document . createElement(''div'');
  e . setAttribute(''id'', TEST_ID);
  tmp0 \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(tmp0, None, ''should be null'');
  tmp1 \<leftarrow> document . body;
  tmp1 . appendChild(e);
  tmp2 \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(tmp2, e, ''should be the appended element'')
}) Document_getElementById_heap"
  by eval


text \<open>"in tree order, within the context object's tree"\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test5'';
  target \<leftarrow> document . getElementById(TEST_ID);
  assert_not_equals(target, None, ''should not be null'');
  tmp0 \<leftarrow> target . getAttribute(''data-name'');
  assert_equals(tmp0, ''1st'', ''should return the 1st'');
  element4 \<leftarrow> document . createElement(''div'');
  element4 . setAttribute(''id'', TEST_ID);
  element4 . setAttribute(''data-name'', ''4th'');
  gBody . appendChild(element4);
  target2 \<leftarrow> document . getElementById(TEST_ID);
  assert_not_equals(target2, None, ''should not be null'');
  tmp1 \<leftarrow> target2 . getAttribute(''data-name'');
  assert_equals(tmp1, ''1st'', ''should be the 1st'');
  tmp2 \<leftarrow> target2 . parentNode;
  tmp2 . removeChild(target2);
  target3 \<leftarrow> document . getElementById(TEST_ID);
  assert_not_equals(target3, None, ''should not be null'');
  tmp3 \<leftarrow> target3 . getAttribute(''data-name'');
  assert_equals(tmp3, ''4th'', ''should be the 4th'')
}) Document_getElementById_heap"
  by eval


text \<open>"Modern browsers optimize this method with using internal id cache. 
    This test checks that their optimization should effect only append to 
    `Document`, not append to `Node`."\<close>

lemma "test (do {
  TEST_ID \<leftarrow> return ''test6'';
  s \<leftarrow> document . createElement(''div'');
  s . setAttribute(''id'', TEST_ID);
  tmp0 \<leftarrow> document . createElement(''div'');
  tmp0 . appendChild(s);
  tmp1 \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(tmp1, None, ''should be null'')
}) Document_getElementById_heap"
  by eval


text \<open>"changing attribute's value via `Attr` gotten from `Element.attribute`."\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test7'';
  element \<leftarrow> document . createElement(''div'');
  element . setAttribute(''id'', TEST_ID);
  gBody . appendChild(element);
  target \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(target, element, ''should return the element before changing the value'');
  element . setAttribute(''id'', (TEST_ID @ ''-updated''));
  target2 \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(target2, None, ''should return null after updated id via Attr.value'');
  target3 \<leftarrow> document . getElementById((TEST_ID @ ''-updated''));
  assert_equals(target3, element, ''should be equal to the updated element.'')
}) Document_getElementById_heap"
  by eval


text \<open>"update `id` attribute via element.id"\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test12'';
  test \<leftarrow> document . createElement(''div'');
  test . setAttribute(''id'', TEST_ID);
  gBody . appendChild(test);
  UPDATED_ID \<leftarrow> return (TEST_ID @ ''-updated'');
  test . setAttribute(''id'', UPDATED_ID);
  e \<leftarrow> document . getElementById(UPDATED_ID);
  assert_equals(e, test, ''should get the element with id.'');
  old \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(old, None, ''shouldn't get the element by the old id.'');
  test . setAttribute(''id'', '''');
  e2 \<leftarrow> document . getElementById(UPDATED_ID);
  assert_equals(e2, None, ''should return null when the passed id is none in document.'')
}) Document_getElementById_heap"
  by eval


text \<open>"where insertion order and tree order don't match"\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test13'';
  container \<leftarrow> document . createElement(''div'');
  container . setAttribute(''id'', (TEST_ID @ ''-fixture''));
  gBody . appendChild(container);
  element1 \<leftarrow> document . createElement(''div'');
  element1 . setAttribute(''id'', TEST_ID);
  element2 \<leftarrow> document . createElement(''div'');
  element2 . setAttribute(''id'', TEST_ID);
  element3 \<leftarrow> document . createElement(''div'');
  element3 . setAttribute(''id'', TEST_ID);
  element4 \<leftarrow> document . createElement(''div'');
  element4 . setAttribute(''id'', TEST_ID);
  container . appendChild(element2);
  container . appendChild(element4);
  container . insertBefore(element3, element4);
  container . insertBefore(element1, element2);
  test \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(test, element1, ''should return 1st element'');
  container . removeChild(element1);
  test \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(test, element2, ''should return 2nd element'');
  container . removeChild(element2);
  test \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(test, element3, ''should return 3rd element'');
  container . removeChild(element3);
  test \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(test, element4, ''should return 4th element'');
  container . removeChild(element4)
}) Document_getElementById_heap"
  by eval


text \<open>"Inserting an id by inserting its parent node"\<close>

lemma "test (do {
  gBody \<leftarrow> document . body;
  TEST_ID \<leftarrow> return ''test14'';
  a \<leftarrow> document . createElement(''a'');
  b \<leftarrow> document . createElement(''b'');
  a . appendChild(b);
  b . setAttribute(''id'', TEST_ID);
  tmp0 \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(tmp0, None);
  gBody . appendChild(a);
  tmp1 \<leftarrow> document . getElementById(TEST_ID);
  assert_equals(tmp1, b)
}) Document_getElementById_heap"
  by eval


text \<open>"Document.getElementById must not return nodes not present in document"\<close>

lemma "test (do {
  TEST_ID \<leftarrow> return ''test15'';
  outer \<leftarrow> document . getElementById(''outer'');
  middle \<leftarrow> document . getElementById(''middle'');
  inner \<leftarrow> document . getElementById(''inner'');
  tmp0 \<leftarrow> document . getElementById(''middle'');
  outer . removeChild(tmp0);
  new_el \<leftarrow> document . createElement(''h1'');
  new_el . setAttribute(''id'', ''heading'');
  inner . appendChild(new_el);
  tmp1 \<leftarrow> document . getElementById(''heading'');
  assert_equals(tmp1, None)
}) Document_getElementById_heap"
  by eval


end
