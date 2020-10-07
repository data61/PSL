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

section\<open>References\<close>
text\<open>
  This theory, we introduce a generic reference. All our typed pointers include such 
  a reference, which allows us to distinguish pointers of the same type, but also to 
  iterate over all pointers in a set.\<close>
theory 
  Ref
  imports
    "HOL-Library.Adhoc_Overloading"
    "../preliminaries/Hiding_Type_Variables"
begin

instantiation sum :: (linorder, linorder) linorder
begin
definition less_eq_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
  where
    "less_eq_sum t t' = (case t of
      Inl l \<Rightarrow> (case t' of
        Inl l' \<Rightarrow> l \<le> l'
      | Inr r' \<Rightarrow> True)
    | Inr r \<Rightarrow> (case t' of
        Inl l' \<Rightarrow> False
      | Inr r' \<Rightarrow> r \<le> r'))"
definition less_sum :: "'a + 'b \<Rightarrow> 'a + 'b \<Rightarrow> bool"
  where
    "less_sum t t' \<equiv> t \<le> t' \<and> \<not> t' \<le> t"
instance by(standard) (auto simp add: less_eq_sum_def less_sum_def split: sum.splits)
end

type_synonym ref = nat
consts cast :: 'a

end
