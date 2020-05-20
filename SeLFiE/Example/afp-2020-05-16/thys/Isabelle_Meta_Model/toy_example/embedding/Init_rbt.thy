(******************************************************************************
 * Citadelle
 *
 * Copyright (c) 2011-2018 Université Paris-Saclay, Univ. Paris-Sud, France
 *               2013-2017 IRT SystemX, France
 *               2011-2015 Achim D. Brucker, Germany
 *               2016-2018 The University of Sheffield, UK
 *               2016-2017 Nanyang Technological University, Singapore
 *               2017-2018 Virginia Tech, USA
 *
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are
 * met:
 *
 *     * Redistributions of source code must retain the above copyright
 *       notice, this list of conditions and the following disclaimer.
 *
 *     * Redistributions in binary form must reproduce the above
 *       copyright notice, this list of conditions and the following
 *       disclaimer in the documentation and/or other materials provided
 *       with the distribution.
 *
 *     * Neither the name of the copyright holders nor the names of its
 *       contributors may be used to endorse or promote products derived
 *       from this software without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
 * A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
 * OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
 * SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
 * LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 ******************************************************************************)

section\<open>Basic Extension of the Standard Library (Depending on RBT)\<close>

theory Init_rbt
imports "../../Init"
        "HOL-Library.RBT"
        "HOL-Library.Char_ord"
        "HOL-Library.List_Lexorder"
begin

locale RBT
begin
definition "modify_def v k f rbt =
  (case RBT.lookup rbt k of None \<Rightarrow> RBT.insert k (f v) rbt
                      | Some _ \<Rightarrow> RBT.map_entry k f rbt)"
definition "lookup2 rbt = (\<lambda>(x1, x2). Option.bind (RBT.lookup rbt x1) (\<lambda>rbt. RBT.lookup rbt x2))"
definition "insert2 = (\<lambda>(x1, x2) v. RBT.modify_def RBT.empty x1 (RBT.insert x2 v))"
end
lemmas [code] =
  \<comment> \<open>def\<close>
  RBT.modify_def_def
  RBT.lookup2_def
  RBT.insert2_def

context L
begin
definition "unique f l = List.map_filter id (fst
  (mapM
    (\<lambda> (cpt, v) rbt. 
      let f_cpt = f cpt in
      if RBT.lookup rbt f_cpt = None then
        (Some (cpt, v), RBT.insert f_cpt () rbt)
      else 
        (None, rbt))
    l
    RBT.empty))"
end
lemmas [code] =
  \<comment> \<open>def\<close>
  L.unique_def

end
