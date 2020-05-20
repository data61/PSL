(******************************************************************************
 * A Meta-Model for the Isabelle API
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

section\<open>(Pure) Term Meta-Model aka. AST definition of (Pure) Term\<close>

theory  Meta_Pure
imports "../Init"
begin

subsection\<open>Type Definition\<close>

type_synonym indexname = "string \<times> nat"
type_synonym "class" = string
type_synonym sort = "class list"
datatype "typ" =
  Type string "typ list" |
  TFree string sort |
  TVar indexname sort
datatype "term" =
  Const string "typ" |
  Free string "typ" |
  Var indexname "typ" |
  Bound nat |
  Abs string "typ" "term" |
  App "term" "term" (infixl "$" 200)

subsection\<open>Operations of Fold, Map, ..., on the Meta-Model\<close>

fun map_Const where
   "map_Const f expr = (\<lambda> Const s ty \<Rightarrow> Const (f s ty) ty
                        | Free s ty \<Rightarrow> Free s ty
                        | Var i ty \<Rightarrow> Var i ty
                        | Bound n \<Rightarrow> Bound n
                        | Abs s ty term \<Rightarrow> Abs s ty (map_Const f term)
                        | App term1 term2 \<Rightarrow> App (map_Const f term1)
                                                         (map_Const f term2))
                        expr"

fun fold_Const where
   "fold_Const f accu expr = (\<lambda> Const s _ \<Rightarrow> f accu s 
                              | Abs _ _ term \<Rightarrow> fold_Const f accu term
                              | App term1 term2 \<Rightarrow> fold_Const f (fold_Const f accu term1) term2
                              | _ \<Rightarrow> accu)
                               expr"

fun fold_Free where
   "fold_Free f accu expr = (\<lambda> Free s _ \<Rightarrow> f accu s 
                             | Abs _ _ term \<Rightarrow> fold_Free f accu term
                             | App term1 term2 \<Rightarrow> fold_Free f (fold_Free f accu term1) term2
                             | _ \<Rightarrow> accu)
                              expr"

end
