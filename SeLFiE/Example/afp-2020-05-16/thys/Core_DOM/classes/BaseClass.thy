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

section\<open>The Class Infrastructure\<close>
text\<open>In this theory, we introduce the basic infrastructure for our encoding 
of classes.\<close>
theory BaseClass
  imports
    "HOL-Library.Finite_Map"
    "../pointers/Ref"
    "../Core_DOM_Basic_Datatypes" 
begin

named_theorems instances

consts get :: 'a
consts put :: 'a
consts delete :: 'a

text \<open>Overall, the definition of the class types follows closely the one of the pointer 
  types. Instead of datatypes, we use records for our classes. This allows us to, first, 
  make use of record inheritance, which is, in addition to the type synonyms of
  previous class types, the second place where the inheritance relationship of 
  our types manifest. Second, we get a convenient notation to define classes, in
  addition to automatically generated getter and setter functions.\<close>

text \<open>Along with our class types, we also develop our heap type, which is a finite 
  map at its core. It is important to note that while the map stores a mapping 
  from @{term "object_ptr"} to @{term "Object"}, we restrict the type variables 
  of the record extension slot of @{term "Object"} in such a way that allows 
  down-casting, but requires a bit of taking-apart and re-assembling of our records 
  before they are stored in the heap.\<close>

text \<open>Throughout the theory files, we will use underscore case to reference pointer 
      types, and camel case for class types.\<close>

text \<open>Every class type contains at least one attribute; nothing. This is used for 
  two purposes: first, the record package does not allow records without any 
  attributes. Second, we will use the getter of nothing later to check whether a 
  class of the correct type could be retrieved, for which we will be able to use
  our infrastructure regarding the behaviour of getters across different heaps.\<close>


locale l_type_wf = fixes type_wf :: "'heap \<Rightarrow> bool"

locale l_known_ptr = fixes known_ptr :: "'ptr \<Rightarrow> bool"

end
