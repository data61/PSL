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

section\<open>Object\<close>
text\<open>In this theory, we introduce the typed pointer for the class Object. This class is the 
common superclass of our class model.\<close>
theory ObjectPointer
  imports
    Ref
begin

datatype 'object_ptr object_ptr = Ext 'object_ptr
register_default_tvars "'object_ptr object_ptr" 

instantiation object_ptr :: (linorder) linorder
begin
definition less_eq_object_ptr :: "'object_ptr::linorder object_ptr \<Rightarrow> 'object_ptr object_ptr \<Rightarrow> bool"
  where "less_eq_object_ptr x y \<equiv> (case x of Ext i \<Rightarrow> (case y of Ext j \<Rightarrow> i \<le> j))"
definition less_object_ptr :: "'object_ptr::linorder object_ptr \<Rightarrow> 'object_ptr object_ptr \<Rightarrow> bool"
  where "less_object_ptr x y \<equiv> x \<le> y \<and> \<not> y \<le> x"
instance by(standard, auto simp add: less_eq_object_ptr_def less_object_ptr_def 
      split: object_ptr.splits)
end

end
